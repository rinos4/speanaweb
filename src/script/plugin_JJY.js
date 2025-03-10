////////////////////////////////////////////////////////////////////////////////
// plugin_JJY: JJY decode plugin for SpeAnaWEB
// Copyright (c) 2012 rinos4u, released under the MIT open source license.
////////////////////////////////////////////////////////////////////////////////

// for lint...
/*
var console;
var alert;
var getRange, toDB;
//*/

////////////////////////////////////////////////////////////////////////////////
// JJY decode plugin
////////////////////////////////////////////////////////////////////////////////
var PluginJJY = (function () {
    'use strict';
    
    var JJY_FREQ    = 40000;        // 40kHz位置
    var MIN_SR      = JJY_FREQ * 2; // ナイキスト周波数で40kHzが必要。多分96kHz入力を使用。
    var REC_BLOCK   = 16384;        // 96kHzで分解能11.7Hzになる(アンテナ利得によるが10Hz推奨)
    var JJY_DIV     = 2;            // 0.05秒分割で同期
    var JJY_STEP    = 10 * JJY_DIV; // 分割数 (10の倍数)
    var SYNC_SAME   = 1;            // オフセットが1回連続同じ場所なら同期完了
    //var DEC_TABLE   = ['M', 'M', 'M', 'M', '1', '1', '1', '0', '0', '0', '0', 'X'];
    var DEC_TABLE   = ['M', 'M', 'M', '1', '1', '1', '1', '0', '0', '0', '0', 'X'];
    var WEEK_NAME   = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];

    // Threshold settings
    var TH_POS      = 2 / 3;        // 最小値はノイズ変動が大きいため2/3の位置を閾値に設定
    //var TH_KEEP     = 90 /100;      // 過去の閾値の重みづけ
    var TH_KEEP     = 50 /100;      // 過去の閾値の重みづけ

    // SpeAna objs
    var model;
    var view;
    var idTone;
    var idWaveCanvas;
    var idOverlap;
    var idFFTSel;

    // Parameter set/backup for JJY plugin /////////////////////////////////////
    var restore_flag;
    var jjy_params;
    function initParams(model, view, elm) {
        if (jjy_params) return; // already init
        jjy_params = [
            [model,         'fft_size',     REC_BLOCK],
            [model,         'fft_overlap'], 
            [elm.idOverlap, 'disabled',     true],
            [elm.idFreqMin, 'value',        38.5],
            [elm.idFreqMax, 'value',        41.5],
            [elm.idAmplMin, 'value',        -110.0],
            [elm.idAmplMax, 'value',        -80.0],
            [view,          'flow_speed',   1],
        ];
    }
    function saveParams(save) {
        var src = save? 2 : 3;
        var dst = save? 3 : 2;
        jjy_params.forEach(function (v) {
            v[dst] = v[0][v[1]];
            if (v[src] !== undefined) v[0][v[1]] = v[src];
            //console.log(v[1], v[dst], ' -> ', v[src]);
        });
        view.changeFreqRange(3); // update range
        view.changeAmplRange(3); // update range
        restore_flag = save;
    }


    // JJY decode parameters ///////////////////////////////////////////////////
    var stepbuf;    // JJY周波数の直値を格納するバッファ
    var steppos;    // バッファの最終格納位置
    var fdsskip;    // フロースピード有り時のスキップカウンタ
    var sync;       // 同期位置
    var synccnt;    // 現在の同期カウント
    var curthr;     // 現在の閾値
    var decbuf;     // デコードバッファ
    var mmsync;     // MMマーカ同期
    var jjypos;     // JJY信号格納の配列位置
    var jjymod;     // JJY信号の補完位置
    var decbyte;    // マーカ後のデコードバイト
    var jjytime;    // デコードした時刻
    var fixtime;    // 確定時刻
    var pre_x;      // 直前の描画位置(グラフ連結用)

    // JJY decoder /////////////////////////////////////////////////////////////
    function reset_params() {
        stepbuf = [];
        steppos = 0;
        fdsskip = 0;
        sync    = JJY_STEP + 1; // not sync (invalid value)
        synccnt = 0;
        curthr  = false;
        decbuf  = "";
        mmsync  = 0;
        jjymod  = model.fft_size * JJY_FREQ / model.buf_sr;
        jjypos  = jjymod | 0;
        jjymod -= jjypos;
        decbyte = 0;
        jjytime = [];
        fixtime = 'Not fixed';
        pre_x   = false;
        //console.log('PluginJJY reset ', jjypos, jjymod);
    }

    // JJY configration methods ////////////////////////////////////////////////
    function setOverlap() {
        //console.log('PluginJJY setOverlap');
        var sr = model.buf_sr;
        model.fft_overlap = 1 - (sr? sr : MIN_SR) / model.fft_size / JJY_STEP;
    }

    // Plugin methods //////////////////////////////////////////////////////////
    function initPlugin(m, v, elm) {
        console.log('PluginJJY init');
        model = m;
        view  = v;

        idWaveCanvas = elm.idWaveCanvas;
        idTone       = (elm.idTone && elm.idTone.src)? elm.idTone : null;
        idOverlap    = elm.idOverlap;
        idFFTSel     = elm.idFFTSel;
        initParams(model, view, elm);
        
        // Check the availability of source input
        if (!changeSrc(true)) {
            // Bad input source for JJY...
            deinitPlugin();
            return false; // init fail (plugin will be unloaded)
        }

        // Save current FFT parameters
        saveParams(true);
        
        setOverlap();
        reset_params();
        changeSize();
        changeVolume();
        return true; // init success
    }

    function deinitPlugin() {
        console.log('PluginJJY deinit');
        // Restore FFT parameters which saved at init
        if (restore_flag) saveParams(false);
    }
    
    // Update callbacks ////////////////////////////////////////////////////////
    function changeSrc(check_only) {
        //console.log('PluginJJY changeSrc');
        var sr = model.buf_sr;
        if (sr && sr < MIN_SR) {
            alert('JJY decoder requires more than ' + (MIN_SR / 1000) + 'kHz sample rate for input source.\nJJY plugin will be turned off.');
            return false;
        }
        if (!check_only) setOverlap();
        return true;
    }
    
    function changeBlockSize() {
        //console.log('PluginJJY changeBlockSize');
        setOverlap();
    }
    
    function changeAmpl() {
        //console.log('PluginJJY changeAmpl');
        reset_params();
    }

    function changeFlowSpeed() {
        if (view.flow_speed < 1){
            view.flow_speed = 1; // flow speed must be bigger than 1 for JJY
        }
    }

    // JJY tone playback
    function changeVolume() {
        //console.log('PluginJJY changeVolume', view.volume);
        if(idTone) idTone.volume = view.volume;
    }
    function pbRewind() {
        reset_params();
    }
    function pbPlay() {
        //console.log('PluginJJY play');
        if (idTone) {
            idTone.loop         = true;
            idTone.currentTime  = 0;
        }
    }
    function pbStop() {
        if (idTone) idTone.pause();
    }

    // JJY drawings ////////////////////////////////////////////////////////////
    // screen parameter cache
    var jjy_x;
    var jjy_x2;
    var jjy_h;
    var jjy_w;
    var jjy_w2;
    var FONT_H = 8;

    function changeSize() {
        jjy_x  = view.wave_w + 1;
        jjy_h  = view.ctx_wave.canvas.height;
        jjy_w  = view.ctx_flow.canvas.width - jjy_x - 1;
        jjy_w2 = jjy_w / 2;
        jjy_x2 = jjy_x + 40;
    }

    function getPosX(v) {
        var ampl_ary = view.ampl_ary;
        return jjy_x + jjy_w2 + jjy_w2 * getRange((v - ampl_ary.min) / ampl_ary.width, 0, 1);
    }

    // Draw JJY signal and decode information
    function drawJJY(y, inv){
        var label_y = y + (inv? 0 : 8);

        // Get JJY (40kHz) signal value from FFT spectrum array
        var curval = model.spec_low[jjypos] * (1 - jjymod) + model.spec_low[jjypos + 1] * jjymod;
        if (view.ampl_mode) curval = toDB(curval);

        // Fix情報があればWave右端に表示しておく
        var ctx_wave = view.ctx_wave;
        ctx_wave.fillStyle = '#600';
        ctx_wave.fillRect(jjy_x2, jjy_h / 2, jjy_w, FONT_H * 2);
        ctx_wave.fillStyle = '#8f8';
        ctx_wave.fillText(fixtime, jjy_x2, jjy_h / 2 + FONT_H * 1.5);

        // 右ペインに40kHzのSignalも1ライン描画
        var ctx_flow = view.ctx_flow;
        var cur_x = getPosX(curval);
        if (pre_x) {
            ctx_flow.fillStyle = steppos? '#0f6' : '#f06';
            ctx_flow.fillRect(Math.min(pre_x, cur_x), y, Math.abs(pre_x - cur_x) + 1, 1);
        }
        pre_x = cur_x;

        // 閾値描画
        if (curthr) {
            ctx_flow.fillStyle = '#ff4';
            ctx_flow.fillRect(getPosX(curthr), y, 2, 1);

            // トーン鳴動
            if (idTone) {
                if (curval > curthr) idTone.play();
                else                 idTone.pause();
            }
        }
        
        // flow_speed>1の時は飛ばす (1未満には設定されない)
        if (++fdsskip < view.flow_speed) return;
        fdsskip = 0;
    
        // 同期完了時は同期オフセットまで読み飛ばす
        if (sync < 0) {
            ++sync;
            //console.log('PluginJJY sync', sync);
            return;
        }

        // 同期判定用の1秒バッファが埋まっていなければ判定しない
        stepbuf[steppos++] = curval;
        if (steppos < JJY_STEP) {
//          console.log('PluginJJY drawFlow:', (curval > curthr)? 1 : 0, ' Val:' + curval, ' Th:' + curthr);
            return;
        }
        steppos = 0;

        // 閾値計算 (同期前でも平均化のため計算しておく)
        var t = Math.min.apply(0, stepbuf) * (1 - TH_POS) + Math.max.apply(0, stepbuf) * TH_POS;
        curthr = curthr? curthr * TH_KEEP + t * (1 - TH_KEEP) : t; // 重み付けで閾値決定

        ctx_flow.fillStyle = '#bef';

        // 未同期 : 最大UPエッジを同期ポイントにする
        if (sync > 0) {
            var max = stepbuf[0] - stepbuf[JJY_STEP - 1];
            var j   = JJY_STEP;
            for (var i = 1; i < JJY_STEP; ++i) {
                var sub = stepbuf[i] - stepbuf[i - 1];
                if (max < sub) {
                    max = sub;
                    j   = i;
                }
            }
            if (sync !== j) { // 同期ポイント変更
                sync = j;
                synccnt = 1; // カウントし直し
            } else if (++synccnt > SYNC_SAME)  {
                sync = -j; // 同期位置決定
            }
            ctx_flow.fillText('Sync: ' + j + ((sync < 0)? ' OK' : '-' + synccnt), jjy_x2, label_y);
            //console.log('PluginJJY drawFlow:' + curval, ' Th:' + curthr, 'sync:' + sync);
            return;
        }

        // 次のコードを計算
        var cnt = 0;
        stepbuf.forEach(function (v) {
            if (v > curthr) ++cnt;
        });
        var ch = DEC_TABLE[cnt / JJY_DIV | 0];
        var msg = ch + ' (' + cnt + ')';

        // コール中判定
        if (mmsync < 0) {
            if (++mmsync < -9) msg = 'call';
        } else {
            if (ch === 'M') {
                if(decbuf.substr(-1) === 'M') {
                    mmsync = 1;
                    //          0     1   2   3   4    5   6    7   8     9  10  11  12  13   14   15  16  17  18
                    jjytime = ['20', 'Y','Y','/','MM','/','DD',' ','WWW',' ','h','h',':','m','m', ' *','d','d','d'];
                    msg += ' MM-Sync';
                    decbyte = 0;
                } else {
                    decbyte = decbyte * 2 + 1; // near 1...
                }
                decbuf  = 'M'; // reset
            } else {
                decbuf += ch;
                decbyte = decbyte * 2 + (ch - '0');
            }
            
            var JJY_PARSER = {
                 4:[13,5],  9:[14,9],               // mm
                14:[10,2], 19:[11,9],               // hh
                24:[16,3], 29:[17,9], 34:[18,9],    // ddd
                45:[ 1,1], 49:[ 2,9],               // YY
            };
            if(mmsync) {
                var pos = JJY_PARSER[mmsync++];
                if (pos) {
                    decbyte &= 0x1f;
                    for (var bit = 0x10; decbyte > pos[1] && bit; bit >>=1) decbyte &= ~bit;
                    jjytime[pos[0]] = '' + decbyte;
                    decbyte = 0;
                    if (mmsync === 50) { // 月日確定
                        console.log('Fix time');
                        var str = jjytime.join('');
                        var dt  = new Date(str.substr(0, 4), 0, str.substr(-3));
                        jjytime[4] = ('0' + (dt.getMonth() + 1)).substr(-2);
                        jjytime[6] = ('0' +  dt.getDate()      ).substr(-2);
                        jjytime[8] = WEEK_NAME[dt.getDay()];
                        fixtime = jjytime.join('').substr(0, 20);
                        msg += ' ' + fixtime + ' Fixed';
                    } else {
                        msg += ' ' + jjytime.join('').substr(2);
                    }
                } else if (mmsync === 41 && jjytime[14] == '5' && (jjytime[13] == '1' || jjytime[13] == '4')) {
                    mmsync = -19; // call start
                    decbuf = '';
                }
            }
        }
        ctx_flow.fillText(msg, jjy_x2, label_y);
        //console.log('PluginJJY drawFlow:', decbyte, mmsync, jjytime.join(''), decbuf);
    }

    return {
        // Plugin methods
        init:           initPlugin,
        deinit:         deinitPlugin,
        draw:           drawJJY,        // call per flow line

        // update notifications
        fft_src:        changeSrc,
        fft_block_size: changeBlockSize,
        volume:         changeVolume,
        resize:         changeSize,
        ampl_mode:      changeAmpl,
        flow_speed:     changeFlowSpeed,

        rewind:         pbRewind,
        play:           pbPlay,
        stop:           pbStop,
        pause:          pbStop, // same as stop for JJY plugin
        
        // Plugin parameters
        hide_signal:    true, // Avoid the drawing of wave signal on the right side of flow canvas
    };
})();
