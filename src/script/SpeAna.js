////////////////////////////////////////////////////////////////////////////////
// SpeAna.js: Spectrum analyzer for WEB
// Copyright (c) 2012 rinos4u, released under the MIT open source license.
////////////////////////////////////////////////////////////////////////////////

/* // for lint...
var window, document, event, navigator, console;
var DataView, Uint8Array, Float32Array;
var WebSocket;
var setTimeout, clearTimeout, alert;
var FileReader, URL, XMLHttpRequest;
var FFT, WaveDecoder;
var getRange, toDB, arrayComp;
//*/

var gdbg = {};

////////////////////////////////////////////////////////////////////////////////
// SpeAnaWeb Object
////////////////////////////////////////////////////////////////////////////////
var SpeAnaWeb = (function () {
    'use strict';

    // var values for SpeAna /////////////////////////////////////////////////
    // Minimum Ampl for log mode
    var MIN_dB     = -120;
    var LOG_START  = 10 / 1000; // Log graph step base is 10Hz, same as freq min step.
    var LOG_STAINV = 1 / LOG_START;
    
    var BUFFER_MS  = 200; // for stream input
    
    ////////////////////////////////////////////////////////////////////////////
    // Plugins
    var plugin = {}; // none

    ////////////////////////////////////////////////////////////////////////////
    // Model Object (FFT calculation object is defined in outer JS)
    ////////////////////////////////////////////////////////////////////////////
    var model = (function () {
        // reset options for statistics (max/avg)
        var RESET_AT_REWIND  = true;
        var RESET_AT_OVERLAP = false;

        var updateCB; // for observer

        // FFT buffer object
        var fftbuf = (function () {
            // Default configuration of FFT
            var src_buf     = null;
            var src_ch      = 1;
            var block_size  = 2;
            var block_half  = block_size >> 1;
            var winfn       = "rect";
            var overlap     = 0;
            var fftobj      = FFT.create(block_size, FFT[winfn]);
            var fftstep     = 0;
            var maxary      = [[], [], false];
            var avgary      = [[], [], false];
            var addcnt      = 0;
            var nextstep    = 0;

            // get specified channel buffer
            function getBuf(start, end, ch){
                if(ch === undefined) ch = src_ch;
                if (src_buf.getChannelData) { // Normal buffer
                    return ((0 < ch && ch <= src_buf.numberOfChannels) ? src_buf.getChannelData(ch - 1) : (src_buf.merge || src_buf.getChannelData(0))).subarray(start, end);
                } else { // Stream buffer
                    return src_buf.getBuf(start, end, ch);
                }
            }

            // Reset Max/Avg ary
            function resetStatistics() {
                addcnt = 0;
                maxary[2] = avgary[2] = false; // duty
                // skip clear of Float32Arrays
                if(src_buf) transAll(nextstep + 1, true);
            }

            // Set source buffer
            function setSrc(buf) {
                // Replace src buffer, and reset position and statstics
                src_buf = buf;
                nextstep = 0;

                // Check channel number to judge whether to make merge buffer
                var ch = buf.numberOfChannels;
                if (src_ch > ch) src_ch = 0;    // Set merge-ch if src channel will be out of range

                // Create merge buffer for multiple channel input (normal buffer only)
                if(buf.getChannelData && !buf.merge && ch > 1) {
                    var len   = buf.length;
                    var merge = new Float32Array(buf.getChannelData(0)); // init by ch-1

                    // Add all other channel
                    for (var i = 1 ; i < ch; ++i){
                        var cdat = buf.getChannelData(i);
                        for (var j = 0; j < len ; ++j) merge[j] += cdat[j];
                    }
                    
                    // average
                    var invn = 1 / ch;
                    for (i = 0; i < len ; ++i) merge[i] *= invn;
                    buf.merge = merge;
                }
                resetStatistics();
            }

            // Re-create the size related objects
            function setBlockSize(size) {
                block_size  = size;
                block_half  = size >> 1;
                fftstep     = size * (1 - overlap); // integer!
                fftobj      = FFT.create(size, FFT[winfn]);
                maxary      = [new Float32Array(block_half), new Float32Array(block_half), false];
                avgary      = [new Float32Array(block_half), new Float32Array(block_half), false];
                resetStatistics();
            }
            
            // Set channel
            function numCh() {
                return src_buf? src_buf.numberOfChannels : 0;
            }
            function setCh(ch) {
                // Set merge-ch if src channel will be out of range
                src_ch = (numCh() < ch)? 0 : ch;
                resetStatistics();
            }

            // Set window function
            function setWindow(wf) {
                winfn = wf;
                fftobj.changeWindow(FFT[wf]);
                resetStatistics();
            }

            // Set overlap ratio
            function setOverlap(v) {
                overlap = v;
                fftstep = block_size * (1 - v); // integer!
                nextstep -= nextstep % fftstep;
                if (RESET_AT_OVERLAP) resetStatistics();
            }

            // Rewind parameters
            function rewind() {
                nextstep = 0;
                if (RESET_AT_REWIND) resetStatistics();
            }

            // Check range of stream buffer
            function inRange(end) {
                var fn = src_buf.inRange;
                return fn ? fn(end) : true;
            }
            
            // Waste the useless buffer area
            function waste(end) {
                var fn = src_buf && src_buf.waste;
                return fn ? fn(end) : true;
            }
            
            // FFT forward translation from specified offset of src buffer
            function transLow(offset) {
                var buf =  getBuf(offset, offset + block_size);
                if (!buf) return false;
                fftobj.trans(buf, 0, false);
                return fftobj.result; // last result
            }

            // Step translation by the specified overlap ratio, and accum statistics (max/avg)
            function transAll(offset, reset) {
                var sstep = nextstep;
                //console.log('transAll', sstep, offset + block_size);
                var buf = getBuf(sstep, offset + block_size);
                if (!buf) return false;
                while(nextstep < offset) {
                    fftobj.trans(buf, nextstep - sstep);
                    nextstep += fftstep;
                    var res = fftobj.result, i;
                    var maxbuf = maxary[0];
                    var avgsum = avgary[0];
                    if (addcnt++) {
                        // add avg-sum and check max
                        for (i = 0; i < block_half; ++i) {
                            avgsum[i] += res[i];
                            if(maxbuf[i] < res[i]) maxbuf[i] = res[i];
                        }
                    } else {
                        // first assignment
                        for (i = 0; i < block_half; ++i) {
                            maxbuf[i] = avgsum[i] = res[i];
                        }
                    }
                    maxary[2] = avgary[2] = false; // clear cache
                    if (reset) break;
                }
                return true;
            }

            // Create and return the result buffer of Max/Avg
            function makeSub(ary, coef) {
                // check cache
                var src = ary[0];
                var dst = ary[1];
                if(ary[2]) return dst;// return cached buffer
                ary[2] = true; // set cached mark

                // Create new result and cache it to dst.
                for (var i = 0; i < block_half; ++i) dst[i] = src[i] * coef;
                return dst;
            }

            // public method
            return {
                // FFT
                transLow:       transLow,
                transAll:       transAll,
                rewind:         rewind,
                inRange:        inRange,
                waste:          waste,
                
                // get buffer of specified channel
                srcbuf:         getBuf,

                // Reset
                resetStatistics:resetStatistics,
                
                // getter for spectrum, use these after calling transAll
                get spec_low()  { return fftobj.result; }, 
                get spec_max()  { return makeSub(maxary, 1); },
                get spec_avg()  { return makeSub(avgary, 1 / addcnt); },
                
                // getter/setter for FFT parameters
                get src()       { return src_buf; },
                set src(v)      { setSrc(v); },
                get size()      { return block_size; },
                set size(v)     { setBlockSize(v); },
                get ch()        { return src_ch; },
                set ch(v)       { setCh(v); },
                get winfn()     { return winfn; },
                set winfn(v)    { setWindow(v); },
                get overlap()   { return overlap; },
                set overlap(v)  { setOverlap(v); },

                // for easy access
                get block_half(){ return block_half; },
                get step()      { return fftstep; },
                get pos()       { return nextstep; },
                get numCh()     { return numCh(); },
            };
        })();

        // Change source data and notify the updateCB
        function changeFFTSrc(src){
            if (fftbuf.src !== src) {
                fftbuf.src = src;
                updateCB({fft_src: true});
            }
        }

        // Change block size and notify the updateCB
        function changeFFTblkSize(size){
            if (fftbuf.size !== (size |= 0)) {
                fftbuf.size = size;
                updateCB({fft_block_size: true});
            }
        }

        // Change target channel and notify the updateCB
        function changeFFTch(ch){
            if(fftbuf.numCh < (ch |= 0)) ch = 0; // range over

            if (fftbuf.ch !== ch) {
                fftbuf.ch = ch;
                updateCB({fft_ch: true});
            }
        }

        // Change window function and notify the updateCB
        function changeFFTWindow(name){
            if (fftbuf.winfn !== name) {
                fftbuf.winfn = name;
                updateCB({fft_window: true});
            }
        }

        // Change overlap ratio and notify the updateCB (direct)
        function changeOverlap(ratio){
            if (fftbuf.overlap !== ratio) {
                fftbuf.overlap = ratio;
                updateCB({fft_overlap: true});
            }
        }
        // Change overlap ratio and notify the updateCB (overlap: 7step; 0% 25% 50% 75% 88% 94% 97%)
        var OVERLAP_RATION = [0.00, 0.25, 0.50, 0.75, 0.875, 0.9375, 0.96875];
        function changeOverlap2(n){
            changeOverlap(OVERLAP_RATION[getRange(n | 0, 0, 6)]);
        }

        // Clear Max/Avg statistics
        function clearStat() {
            fftbuf.resetStatistics();
            updateCB({fft_maxavg: true});
        }

        // public method of model
        return {
            setObserver:        function (fn) { updateCB = fn; },

            // parameter settings
            clearStat:          clearStat,
            
            transAll:           fftbuf.transAll,
            transLow:           fftbuf.transLow,
            rewind:             fftbuf.rewind,
            inRange:            fftbuf.inRange,
            waste:              fftbuf.waste,

            get srcbuf()        { return fftbuf.srcbuf; },
            get src()           { return fftbuf.src; },
            set src(v)          { changeFFTSrc(v); },
            get buf_nch()       { return fftbuf.src? fftbuf.src.numberOfChannels : 0; },
            get buf_bit()       { return fftbuf.src? fftbuf.src.bits             : 0; },
            get buf_len()       { return fftbuf.src? fftbuf.src.length           : 0; },
            get buf_sr()        { return fftbuf.src? fftbuf.src.sampleRate       : 0; },
            get buf_dur()       { return fftbuf.src? fftbuf.src.duration         : 0; },

            get spec_low()      { return fftbuf.spec_low; }, 
            get spec_max()      { return fftbuf.spec_max; }, 
            get spec_avg()      { return fftbuf.spec_avg; }, 
            
            get fft_ch()        { return fftbuf.ch;         },
            set fft_ch(v)       { changeFFTch(v);           },
            get fft_size()      { return fftbuf.size;       },
            set fft_size(v)     { changeFFTblkSize(v);      },
            get fft_half()      { return fftbuf.block_half; },
            get fft_overlap()   { return fftbuf.overlap;    },
            set fft_overlap(v)  { changeOverlap(v);         },
            get fft_overlap2()  { return null;              }, // error
            set fft_overlap2(v) { changeOverlap2(v);        },
            get fft_step()      { return fftbuf.step;       },
            get fft_winfn()     { return fftbuf.winfn;      },
            set fft_winfn(v)    { changeFFTWindow(v);       },
        };
    })();


    ////////////////////////////////////////////////////////////////////////////
    // View Object
    ////////////////////////////////////////////////////////////////////////////
    // Use elm for cache the DOM which has id: 'idXXX' and window.
    var elm = { window: window };

    // AudioContext (audio_ctx.createAnalyser can't divide channel...?, so use original fft.js as default)
    var audio_ctx;  

    var view = (function() {
        // color bar
        var COLORBAR_SCALE      = 0.8;      // 80% width
        var COLORBAR_BACK_COLOR = '#444';
        var COLORBAR_FONT_COLOR = '#fff';

        // spectrum area
        var FLOW_BG_COLOR       = '#333';
        var WAVE_AREA_COLOR     = '#000';
        var SCALE_COLOR         = '#fff';
        var CH_COLOR            = '#cef';
        var SCALE_BG_COLOR      = '#345';
        var SIGSTD_CENTER_COLOR = '#eef';
        var SIGSEL_CENTER_COLOR = '#f55';
        var SIGSEL_COLOR        = '#fd6';
        var SIGSTD_COLOR        = '#69f';
        var DRAG_COLOR          = '#ffc';
        var DRAG_NG_COLOR       = '#f56';
        var FLOW_BORDER_COLOR   = ['rgba(255, 224, 224, 0.3)', 'rgba(255, 224, 224, 0.9)'];
        var GRID_COLOR          = 'rgba(255, 255, 255, 0.5)';
        var WAVE_OUT_COLOR      = 'rgba(128, 128, 128, 0.7)';
        var PAL_OUT_COLOR       = 'rgba(255, 255, 255, 0.5)';
        var PEAK_COLOR          = 'rgba(255, 255, 0, 0.8)';

        // scale parameter
        var FONT_H              = 4;
        var SCALE_FONT_POS      = 14;
        var SCALE_WIDTH         = 50;
        var SCALE_HEIGHT        = 20;
        var SCALE_TBL           = [10, 3, 3, 3, 3, 7, 3, 3, 3, 3];

        // Drawing parameters
        var ctx_flow;
        var ctx_wave;
        var ctx_color;
        var img_flow;

        // useful vars
        var wave_w  = 1;
        var wave_h  = 1;
        var wave_wR = 1;

        // For performance
        var grid_cache = [];

        // view parameter of peak
        var peak_prems  = 0;

        var pre_t_scale;

        // For debug
        var debug_OSD;
        var debug_FPS;

        // Util funcs for view /////////////////////////////////////////////////
        // Stringizing from float by significant digit number (0 <= keta < 10)
        function float2str(v, keta){
            var pos = (v += '').indexOf('.');
            if (pos < 0){
                pos = v.length;
                v += '.';
            }
            if (keta) keta++;
            return (v + '00000000').substr(0, pos + keta);
        }
        function float2strRound(v, keta){ // round for 3 digit
            return float2str(Math.round(v * 1000) / 1000, keta);
        }

        // Calc kiri-su of v (v > 0)
        var BOUNDS_TBL = [0, 1, 2, 5, 5, 5, 10, 10, 10, 10, 10];
        function boundsVal(v){
            var keta = Math.pow(10, Math.floor(Math.LOG10E * Math.log(v)));
            return BOUNDS_TBL[Math.ceil(v / keta)] * keta;
        }

        // Stringizing msec (hhh:mm:ss:xxx) from sec
        function msecTime(msec, keta){ // keta:0..3
            var ret = '';
            var flag='';
            if (msec < 0){
                flag='-';
                msec = -msec;
            }
            if (keta) ret = '.' + ('00' + msec % 1000).substr(-3).substr(0, keta);
            msec = msec / 1000 | 0;
            for (var i = 0; i < 2 && msec >= 60; ++i){
                ret = ':' + ('0' + msec % 60).substr(-2) + ret;
                msec = msec / 60 | 0;
            }
            return flag + msec + ret;
        }

        ////////////////////////////////////////////////////////////////////////
        // Fill funcs
        function fillRect(ctx, x, y, w, h, rgb){
            if (rgb) ctx.fillStyle = rgb;
            ctx.fillRect(x, y, w, h);
        }
        function fillTextLeft(ctx, str, x, y, rgb){
            if (rgb) ctx.fillStyle = rgb;
            ctx.fillText(str, x, y);
        }
        function fillTextCenter(ctx, str, x, y, rgb, font){
            if (rgb) ctx.fillStyle = rgb;
            if (font) {
                ctx.save(); // font is restore
                ctx.font = font;
            }
            var w = ctx.measureText(str).width;
            ctx.fillText(str, x -  w / 2, y);
            if (font) ctx.restore();
            return w; // return length
        }
        function fillTextRight(ctx, str, x, y, rgb){
            if (rgb) ctx.fillStyle = rgb;
            var w = ctx.measureText(str).width;
            ctx.fillText(str, x - w, y);
            return w;
        }
        function fillPolygon(ctx, vec, rgb){
            if (rgb) ctx.fillStyle = rgb;
            ctx.beginPath();
            ctx.moveTo(vec[0], vec[1]);
            for (var i = 2; i < vec.length; i += 2) ctx.lineTo(vec[i] + vec[0], vec[i + 1] + vec[1]);
            ctx.fill();
        }

        // Color palette ///////////////////////////////////////////////////////
        var COLOR_PALETTE = {
            spectrum:      [[128,   0, 128, -128,    0,  128],   // #808 violet
                            [  0,   0, 255,    0,  255,    0],   // #00F blue
                            [  0, 255, 255,    0,    0, -255],   // #0FF cyan
                            [  0, 255,   0,  255,    0,    0],   // #0F0 green
                            [255, 255,   0,    0, -255,    0]],  // #FF0 yellow - #F00 red

            grayscale:     [[  0,   0,   0,  255,  255,  255]],  // #000 black  - #FFF white

            sunset:        [[  0,   0, 255,  255,    0, -255]],  // #00F blue   - #F00 red

            highhue:       [[  0,   0,   0,    0,    0,  255],   // #000 black
                            [  0,   0, 255,  255,    0, -255],   // #00F blue
                            [255,   0,   0,    0,  255,    0],   // #F00 red
                            [255, 255,   0,    0,    0,  255]],  // #FF0 yellow - #FFF white

            temperature:   [[255,   0,   0,    0,  255,    0],   // #F00 red
                            [255, 255,   0,    0,    0,  255],   // #FF0 yellow
                            [255, 255, 255, -255,    0,    0],   // #FFF white
                            [  0, 255, 255,    0, -128,  255]],  // #0FF cyan   - #FF8 blue
        };

        // Color palette generator object
        var PaletteGen = (function() {
            function create(pal, invert){
                // Create rgb table cache for performance
                var cache = [];
                (function init(pal, invert) {
                    var n   = invert? (pal.length * 256 - 1) : 0;
                    var add = invert? -1 : 1;
                    for (var i = 0, j; (j = pal[i]); ++i){
                        for (var k = 0 ; k < 256 ; ++k){
                            var nk = k / 256;
                            cache[n] = [j[0] + j[3] * nk | 0,
                                        j[1] + j[4] * nk | 0,
                                        j[2] + j[5] * nk | 0];
                            n += add;
                        }
                    }
                })(pal, invert);

                // RGB num table for Canvas Image
                function getColor(v) {
                    if (v < 0) return cache[0];
                    var len = cache.length - 1;
                    if (v >=1) return cache[len];
                    return cache[v * len | 0];
                }

                // RGB string for Canvas Context
                function getRGB(v){
                    var c = getColor(v);
                    return 'rgb(' + c[0] + ',' + c[1] + ',' + c[2] + ')';
                }

                // public method
                return {
                    color:  getColor,
                    rgb:    getRGB
                };
            }

            // public method
            return {
                create: create
            };
        })();

        // Audio player of view ////////////////////////////////////////////////
        var audioplayer = (function(){
            // selected type for playback
            var player_type;
            var play_speed  = 1;
            var play_volume = 1;

            var state = 1; // 0:play, 1:stop, 2:pause
            var start_time;
            var timer_pre;
            var timer_end;

            // for AudioContext
            var src_dat;
            var ctx_src;

            function setSrc(src) {
                if (src.opt) {
                    player_type = 3;        // Use on-demand stream buffer
                    src_dat = src;
                } else if (elm.idAudio) {
                    elm.idAudio.src = src;  // Use Audio tag element
                    player_type = 1;
                } else if(audio_ctx) {
                    src_dat = src;
                    player_type = 2;        // Use AudioContext of Web Audio API
                } else {
                    player_type = 0;        // Can't play...
                }
            }

            function setSpeed(v) {
                if (v !== undefined) play_speed = v;
                
                switch (player_type) {
                case 1: // Use Audio tag
                    elm.idAudio.playbackRate        = play_speed;
                    break;

                case 2: // Use AudioContext of Web Audio API
                    if (ctx_src) {
                        ctx_src.playbackRate.value  = play_speed;
                    }
                    break;

                case 3: // WS Stream
                    // not support
                    break;
                }
            }

            function setVolume(v) {
                if (v !== undefined) play_volume = v;

                switch (player_type) {
                case 1: // Use Audio tag
                    elm.idAudio.volume              = play_volume;
                    break;

                case 2: // Use AudioContext of Web Audio API
                    // Use AudioContext of Web Audio API
                    if (ctx_src) {
                        ctx_src.gain.value          = play_volume;
                    }
                    break;

                case 3: // WS Stream
                    // not support
                    break;
                }

                update({volume: true});
            }

            // Playback
            function timerCB(){
                // Get current position [ms]
                var cur = ((player_type === 1)? elm.idAudio.currentTime * 1000 : (Date.now() - start_time) * play_speed) | 0;
                if (cur > timer_end) cur = timer_end;
                if (cur > timer_pre) {
                    var mSR;
                    if (player_type === 3) {
                        mSR = model.buf_sr / 1000;  // sample/msec
                        var cur_pos = cur * mSR | 0;
                        if (!model.inRange(cur_pos + model.fft_size)) {
                            if (!state) {
                                 // buffer is not ready
                                 start_time += BUFFER_MS;
                                 setTimeout(timerCB, BUFFER_MS);
                                 console.log('Wait for data', BUFFER_MS + 'ms');
                             }
                             return;
                        }
                    }
                    if (drawDelta(cur, timer_pre)) { // progress is success?
                        if (player_type === 3) model.waste(timer_pre * mSR | 0); // TODO cur is bad...?
                        timer_pre = cur;
                    }
                }

                // FPS debug
                if (debug_FPS) drawFPS();

                // Set next callback
                var next = null;
                if (!state){
                    if (cur < timer_end){
                        next = timerCB;
                    } else {
                        if (elm.idRepeat.checked) next = start; // auto repeat
                        stop(elm.idRepeat.checked);
                    }
                }
                if (next) setTimeout(next, 10); // fix
            }

            function play(){
                // Init playback vars
                if (state === 1){ // From begin (not from puased position)
                    model.rewind();

                    timer_pre = -1;
                    if (player_type === 3) {
                        timer_end = Infinity;
                    } else {
                        timer_end = (model.buf_len - model.fft_size) * 1000 / model.buf_sr | 0;
                    }
                    update({play: true, rewind: true});
                } else {
                    update({play: true});
                }

                // Change view of player
                elm.idStart.disabled = true;
                elm.idStop. disabled = false;

                // Start sound
                switch (player_type) {
                case 1: // Use Audio tag
                    setSpeed();
                    setVolume();

                    elm.idPause.disabled = false; // Audio tag can puse
                    elm.idAudio.play();
                    break;

                case 2: // Use AudioContext of Web Audio API
                    // set audio source for AudioContext (ctx_src is disposable, so create this every time)
                    ctx_src        = audio_ctx.createBufferSource();
                    ctx_src.buffer = src_dat;
                    ctx_src.connect(audio_ctx.destination);

                    setSpeed();
                    setVolume();

                    ctx_src.noteOn(0);
                    break;

                case 3: // WS Stream
                    if (src_dat && !src_dat.disable) {
                        src_dat.send('start ' + JSON.stringify(src_dat.opt) + '\n'); // Start mic input
                    }
                    break;
                }

                start_time = Date.now(); // for self timer management (player_type: 2, 3)
                state = 0; // set play state
                timerCB();
            }

            function stop(repeat) {
                // Check current state
                if (state === 1) return;

                switch (player_type) {
                case 1: // Use Audio tag
                    elm.idAudio.pause();
                    elm.idAudio.currentTime = 0; // rewind
                    break;

                case 2: // Use AudioContext of Web Audio API
                    ctx_src.noteOff(0);
                    ctx_src = null; // Destroy the current buffer source (AudioContext can't rewind buffer)
                    break;

                case 3: // WS Stream
                    if (src_dat && !src_dat.disable) {
                        src_dat.send('pause\n'); // Puase mic input
                        model.waste(null); // all
                    }
                    break;
                }

                // Change view of player
                if (!repeat){ // suppress the blinking of control
                    elm.idStart.disabled = false;
                    elm.idStop. disabled = true;
                    elm.idPause.disabled = true;
                }

                update({stop: true});

                state = 1; // set stop state
            }

            function pause() {
                // Check current state
                if (state) return;

                switch (player_type) {
                case 1: // Use Audio tag
                    elm.idAudio.pause();
                    elm.idPause.disabled = true;
                    elm.idStart.disabled = false;
                    break;

                case 2: // Use AudioContext of Web Audio API
                    alert('Not implemented');
                    break;

                case 3: // WS Stream
                    alert('Not implemented');
                    break;
                }

                update({pause: true});

                state = 2; // set pause state
            }

            // public method
            return {
                setSrc:         setSrc,

                play:           play,
                stop:           stop,
                pause:          pause,
                
                get speed()     { return play_speed; },
                set speed(v)    { setSpeed(v); },
                get volume()    { return play_volume; },
                set volume(v)   { setVolume(v); },
                get pstate()    { return state; },
            };
        })();

        ///////////////////////////////////////////////////////////////////////////////
        // View settings
        ///////////////////////////////////////////////////////////////////////////////
        var opt_pal;        // palette cache
        var opt_freq_mode;
        var opt_ampl_mode;
        var opt_freq_full;
        var opt_flow_mode;
        var opt_flow_speed;
        var opt_freq_grid;
        var opt_ampl_grid;
        var opt_time_grid;
        var opt_lerp;
        var opt_no_overlap;
        var opt_show_max;
        var opt_show_avg;
        var opt_show_peak;
        var opt_peak_period;

        // option related vars
        var freq_ary  = {min:0, max:0, width:0};
        var ampl_ary  = {min:0, max:0, width:0};
        var flow_border = 0;

        function changeLerp(flag) {
            opt_lerp = flag? true : false;
            update({lerp: true});
        }
        function changeNoOverlap(flag) {
            opt_no_overlap = flag? true : false;
            update({no_overlap: true});
        }
        function changeWaveMax(flag) {
            opt_show_max = flag? true : false;
            elm.idClear.disabled = !(opt_show_max || opt_show_avg);
            update({showmax: true});
        }
        function changeWaveAvg(flag) {
            opt_show_avg = flag? true : false;
            elm.idClear.disabled = !(opt_show_max || opt_show_avg);
            update({showavg: true});
        }
        function changeWavePeak(flag){
            opt_show_peak = flag? true : false;
            elm.idPeakPeriod.disabled = !opt_show_peak;
            update({showpeak: true});
        }
        function changePeakPeriod(v){
            opt_peak_period = v | 0;
            elm.idPeakPeriodText.innerText = (v / 1000) + ' s';
        }

        ///////////////////////////////////////////////////////////////////////////////
        // Config Menu settings for view
        ///////////////////////////////////////////////////////////////////////////////
        // Audio playback speed (1..19: x1/4-x4)
        var SPEED_RANGE = [1, 1.05, 1.1, 1.2, 1.3, 1.4, 1.5, 2, 3, 4];
        function changePlaybackSpeed(n){
            n = getRange(n | 0, 1, 19);
            n = (n < 10)? (1 / SPEED_RANGE[10 - n]) : SPEED_RANGE[n - 10];
            audioplayer.speed = n;
            update({pbs: true});
        }

        // Audio volume (0..20)
        function changeVolume(n){
            n = getRange(n | 0, 0, 20) * 0.05;
            audioplayer.volume = n;
            update({volume: true});
        }

        // Color palette of flow area (by palette name)
        function changeColor(name, inv){
            opt_pal = PaletteGen.create(COLOR_PALETTE[name], inv);
            update({colorbar: true});
        }

        // Freq/Ampl range config (common)
        function changeRangeSub(changemax, slide, min_range, keta, vmin, vmax, ary){
            if(changemax === 3) slide = 0;
            if (slide) min_range = ary.width;
            ary.min = Math.max(vmin.value, vmin.min);
            ary.max = Math.min(vmax.value, vmax.max);

            // Fix range error
            if (slide || ary.min >= ary.max - min_range){
                if(changemax & 1){
                    // Change min-side
                    var minmax = vmin.max - min_range;
                    if(ary.min > minmax) {
                        ary.min = minmax;
                        ary.max = vmin.max | 0;
                    } else {
                        ary.max = +ary.min + min_range;
                    }
                }
                if(changemax & 2){
                     // Change Max-side
                    var maxmin = +vmin.min + min_range;
                    if(ary.max < maxmin) {
                        ary.min = vmin.min | 0;
                        ary.max = maxmin;
                    } else {
                        ary.min = ary.max - min_range;
                    }
                }
            }
            vmin.value = float2strRound(ary.min, keta);
            vmax.value = float2strRound(ary.max, keta);
            ary.width  = ary.max - ary.min;
        }

        function changeFreqMode(v){
            if(opt_freq_mode === (v |= 0)) return; // not changed
            opt_freq_mode = v;
            update({freq_mode: true});
        }

        // View range settings for Freq
        function changeFreqRange(changemax, force_slide, guide_bar, guide_ng){
            // Call sub-fn for freq change
            changeRangeSub(changemax, elm.idFreqSlide.checked || force_slide,  0.1, 2, elm.idFreqMin, elm.idFreqMax, freq_ary);
            elm.idFreqFull.disabled = ((elm.idFreqMin.min - elm.idFreqMin.value) === 0 && (elm.idFreqMax.max - elm.idFreqMax.value) === 0);
            var neg = !elm.idFreqFull.disabled;
            if (!(opt_freq_full & 2) && opt_freq_full != neg){
                changeFreqFull(neg && elm.idFreqFull.checked); // update is performed in changeFreqFull
            } else {
                update({freq_range: true});
            }
            
            // Guide bar for mouse control
            if(guide_bar) {
                var mh2 = elm.idWaveCanvas.height / 2;
                fillRect(ctx_wave, guide_bar - 1, force_slide? mh2 : 0, 3, mh2, guide_ng? DRAG_NG_COLOR : DRAG_COLOR);
            }
        }

        // Change Fill/Div mode for Freq
        function changeFreqFull(f){
            // redraw scale
            if (f === -1) {
                opt_freq_full ^= 2;
            } else {
                opt_freq_full = f? 1 : 0;
                update({freq_full: true});
            }
        }

        // Freq grid
        function changeFreqGrid(f){
            opt_freq_grid = f;
            update({freq_grid: true});
        }

        function changeAmplGrid(f){
            opt_ampl_grid = f;
            update({ampl_grid: true});
        }

        function changeTimeGrid(f){
            opt_time_grid = f;
            update({time_grid: true});
        }

        function changeFlowMode(){
            opt_flow_mode = [elm.idFlowNone, elm.idFlowRoll, elm.idFlowOver].filter(function(v){ return v.checked; })[0].value | 0;
            update({flow_mode: true});
        }

        function changeAmplMode(v){
            if (opt_ampl_mode === (v |= 0)) return; // Not changed
            opt_ampl_mode = v;
            
            // Rescale each value of min/max element between liner and log mode
            [elm.idAmplMin, elm.idAmplMax].forEach(function(id) {
                if (v) {
                    id.min = MIN_dB;
                    id.max = 0;
                    id.step= 1;
                    id.value = float2strRound(toDB(id.value), 2);
                } else {
                    id.min = 0;
                    id.max = 1;
                    id.step= 0.01;
                    id.value = float2strRound(Math.pow(10, id.value * 0.05), 3);
                }
            });
            elm.idAmplUnit.innerText = v? ' dB' : '';
            changeAmplRange(3);
            update({ampl_mode: true});
        }

        // View range settings for Ampl/Freq
        function changeAmplRange(changemax, force_slide, guide_bar){
            changeRangeSub(changemax, elm.idAmplSlide.checked || force_slide, opt_ampl_mode? 0.1 : 0.01, opt_ampl_mode? 1 : 3, elm.idAmplMin, elm.idAmplMax, ampl_ary);
            update({ampl_range: true});
            
            // Guide bar for mouse control
            if (guide_bar) {
                fillRect(ctx_color, guide_bar - 1, 0, 3, elm.idColorCanvas.height, DRAG_COLOR);
            }
        }

        // v > 0
        function changeFDS(v, noSlide){
            opt_flow_speed = v;
            elm.idFDSText.innerText = (v < 1)? '1/' + 1 / v : 'x' + v;
            if (!noSlide) {
                elm.idFDSRange.value = (v < 1)? 1 - 1 / v : v - 1;
            }
        }
        // n:-19..20  ->  1/20..1/2, 1..20
        function changeFDS2(n, guide_bar, guide_ng){
            changeFDS(((n |= 0) < 0)? 1 / (1 - n) : n + 1, true);
            
            if(audioplayer.pstate) {
                update({fds: true, flow_speed: true});
                fillRect(ctx_flow, 0, guide_bar, elm.idFlowCanvas.width, 2, guide_ng? DRAG_COLOR : DRAG_NG_COLOR); // guide bar
            } else {
                flow_border = 1; // show border at next time
                update({flow_speed: true});
            }
        }

        // debug settings
        function changeOLDebug(f){
            debug_OSD = f;
            elm.idDebugDiv.style.display = f? 'block' : 'none';
        }

        function changeFpsDebug(f){
            debug_FPS = f;
            if (!f) update({fps: true});
        }

        ////////////////////////////////////////////////////////////////////////
        // Linear interpolation transform table (and dest cache) for current canvas-width
        var GMODE_DIV  = 0;
        var GMODE_FUL  = 1;
        var GTYPE_CUR  = 0;
        var GTYPE_MAX  = 1;
        var GTYPE_AVG  = 2;
        var GTYPE_PEAK = 3;
        var lerp_cache = {lerp:[[],[]], param:[], dest:[[[],[],[],{}],[[],[],[],{}]]};

        // Create lerp table if necessary
        function createLerpCache() {
            // Check canvas width
            var mw = wave_w - SCALE_WIDTH;
            if (mw < 2) return; // Canvas has not enough width to draw graph...

            // Check interpolation parameters
            var sr_k = model.buf_sr / 1000;
            var size = model.fft_size - 2;
            var half = size / 2;
            var coef = size / sr_k;
            var logx = opt_freq_mode ? LOG_START : 0;
            var param = [
                freq_ary.min - logx,
                freq_ary.width + logx,
                elm.idFreqMin.min - logx,
                elm.idFreqMin.max - elm.idFreqMin.min + logx,

                // for compare only
                mw,
                coef,
                opt_lerp,
            ];
            if (arrayComp(lerp_cache.param, param)) return; // Same as before
            lerp_cache.param = param;
            logx *= half / param[3];

            // Create both (Div/Full) interpolation table
            lerp_cache.lerp.forEach(function(v, i) {
                var add = param[i * 2    ] * coef;
                var mul = param[i * 2 + 1];
                mul = opt_freq_mode? Math.pow(mul * LOG_STAINV, 1 / mw) : mul  * coef/ (mw + 0.5);
                var f1 = (opt_freq_mode? 1 : mul) + add;
                for (var x = 0; x < mw; ++x) {
                    var f0 = Math.max(f1, 0);
                        f1 = Math.min((opt_freq_mode? Math.pow(mul, x + 1) * logx : (x + 2) * mul) + add, half);
                    var i0 = Math.floor(f0);
                    var i1 = Math.ceil (f1);
                    var ic = (i0 + i1) / 2 + 0.5 | 0; // Use center spectrum for non-lerp mode
                    v[x] = opt_lerp ?   [i0, i1, 1 - (f0 - i0), 1 - (i1 - f1), 1 / (f1 - f0 + 1)] : [ic, ic, 1, 0, 1];
                }
                //console.log('lerp_cache: ', i, mul, (v[0][2]+v[0][3]+v[0][1]-v[0][0]-1) * v[0][4], v[0][3]+v[1][2], v[0], v[1], v[mw - 2], v[mw - 1]);
            });
        }
        
        // Calc specified graph using lerp cache
        function calcDB(val) {
            return opt_ampl_mode? toDB(val) : val;
        }
        function calcLerpSpec(spec, gmode, gtype) {
            // re-create width related table if nesessary or use cache
            createLerpCache();

            // Create graph cache of lerped value
            var mw   = wave_w - SCALE_WIDTH;
            var lerp = lerp_cache.lerp[gmode];
            var dest = lerp_cache.dest[gmode][gtype];
            for (var x = 0; x < mw; ++x) {
                // Linear interpolation
                var ary = lerp[x];
                var i   = ary[0];
                var end = ary[1];
                var val = ary[2] * spec[i] +
                          ary[3] * spec[end]; // end is in scope
                while (++i < end) val += spec[i];
                val *= ary[4];
                /* For blocked max?
                if (gtype === GTYPE_MAX) {
                    var max = Math.max;
                    val = spec[i];
                    while (++i < end) val = max(val, spec[i]); // end is out of scope
                }
                */
                dest[x] = calcDB(val);
            }
            return dest;
        }

        // Calc all graphs specified by option
        function calcLerpValAll(peak) {
            var spec = model.spec_low;
            for (var i = opt_freq_full? 2 : 1; i--;) {
                calcLerpSpec(spec, i, GTYPE_CUR);
                if (opt_show_max) calcLerpSpec(model.spec_max, i, GTYPE_MAX);
                if (opt_show_avg) calcLerpSpec(model.spec_avg, i, GTYPE_AVG);

                if (peak) {
                    var mw   = wave_w - SCALE_WIDTH;
                    var lerp = lerp_cache.lerp[i];
                    var idx  = lerp[0][0];
                    var cand = spec[idx];
                    var cpos = 0;
                    var cHz  = 0;
                    for (var x = 0; x < mw; ++x) {
                        for (var end = lerp[x][1]; idx < end; ++idx) {
                            var val = spec[idx]; // undefined is OK (when FFT block size is changed, udefined will be set)
                            if (cand < val) {
                                cand = val;
                                cpos = x;
                                cHz  = idx;
                            }
                        }
                    }
                    var dest = lerp_cache.dest[i][GTYPE_PEAK];
                    dest.val = cand ? float2strRound(calcDB(cand), 2) + (opt_ampl_mode ? 'dB (' : ' (') + float2strRound(cHz * model.buf_sr / 1000 / (model.fft_size - 2), 2) + 'kHz)' : '';
                    dest.pos = cpos;
                }
            }
        }

        // Color bar ///////////////////////////////////////////////////////////
        function drawColorBar(){
            var width = elm.idColorCanvas.width;

            //debugLog('DrawColorBar ' + width + ', ' + elm.idColorCanvas.height);

            // assign to local var for performance
            var smin = elm.idAmplMin.min;
            var smax = elm.idAmplMax.max;
            var sdif = smax - smin;
            var colh = elm.idColorCanvas.height;
            var y1   = (ampl_ary.min == smin && ampl_ary.max == smax)? colh : (colh / 3 | 0);
            var y2   = elm.idColorCanvas.height - y1;
            var mul  = sdif                  / ampl_ary.width;
            var sub  = (ampl_ary.min - smin) / ampl_ary.width;
            var ctx  = ctx_color;
            
            for (var i = 0 ; i < width ; i++){
                var pos = i / width;
                fillRect(ctx, i, 0, 1, y1, opt_pal.rgb(pos));
                if(y2) fillRect(ctx, i, y2, 1, y1, opt_pal.rgb(pos * mul - sub));
            }
            if (!y2) return; // Not divided mode
            
            // show valid area by poly for divided mode
            fillRect(ctx, 0, y1, width, y2 - y1, COLORBAR_BACK_COLOR);
            sdif = width / sdif;
            var x1 = (ampl_ary.min - smin) * sdif;
            var x2 = (ampl_ary.max - smin) * sdif - width;
            fillPolygon(ctx, [0,    y1,  x1,y1, x1,y2, 0,y2], PAL_OUT_COLOR);
            fillPolygon(ctx, [width,y1,  x2,y1, x2,y2, 0,y2], PAL_OUT_COLOR);

            // Also shows min/max range for divided mode
            var unit = opt_ampl_mode? ' dB' : '';
            var keta = opt_ampl_mode? 1 : 3;
            fillTextLeft (ctx, float2str(ampl_ary.min, keta) + unit, 0,     y2, COLORBAR_FONT_COLOR);    // min (left  side)
            fillTextRight(ctx, float2str(ampl_ary.max, keta) + unit, width, y2);                         // max (right side)
        }

        ////////////////////////////////////////////////////////////////////////
        // Spectrum wave area
        // Wave scale common (for Liner scale)
        function drawScaleSub(ctx, type, x, y, len, scale, minspc){
            var MIN_SCALE = 10000; // freq >= 0.001kHz
            var fmin    = scale.min * MIN_SCALE;
            var fmax    = scale.max * MIN_SCALE;
            var fwidth  = fmax - fmin;
            var mul     = len / fwidth;
            var step    = boundsVal(minspc / mul);
            var cache   = (type? opt_freq_grid : opt_ampl_grid)? grid_cache[type] : 0;
            var keta    = getRange(4 - (step + '').length, 0, 3);
            var inv     = opt_freq_mode? 1 / Math.log(Math.pow((scale.max - scale.min) * LOG_STAINV + 1, 1 / len)) : 0;
            var last    = 0;
            for (var i = fmin - fmin % step; i <= fmax; i += step){
                var p10 = Math.abs(i / step) % 10;
                var s10 = SCALE_TBL[p10];
                var pos = (i - fmin) * mul | 0;
                if (type){ // vertical (Freq)
                    pos = (opt_freq_mode? Math.log((i / MIN_SCALE - scale.min) * LOG_STAINV + 1) * inv | 0 : pos) + x;
                    fillRect(ctx, pos, y, 1, s10);
                    if(!p10){
                        if(cache && pos > x) cache[cache.length] = pos;
                        if(i || !opt_freq_mode) fillTextCenter(ctx, float2str(i / MIN_SCALE, keta), pos, y + 18);
                    } else if (opt_freq_mode && pos - last > (keta + 2) * FONT_H * 2) {
                        fillTextCenter(ctx, float2str(i / MIN_SCALE, keta + 1), pos, y + 18); // sub-label only for log mode
                    }
                    last = pos;
                } else { // horizontal (Ampl)
                    pos = y - pos;
                    fillRect(ctx, x - s10 , pos, s10, 1);
                    if(!p10){
                        fillTextRight(ctx, float2str(i / MIN_SCALE, keta), x - 12, pos + 4);
                        if(cache && pos > 0) cache[cache.length] = pos;
                    }
                }
            }
        }

        // Grid for wave area (use grid_cache, made by drawScaleSub)
        function drawWaveGrid(){
            var ctx = ctx_wave;
            ctx.fillStyle = GRID_COLOR;
            var mw = wave_w - SCALE_WIDTH;
            var mh = wave_h;
            var y = [0,0,0];
            if(opt_freq_full){
                mh = (mh - SCALE_HEIGHT) / 2 | 0;
                y[1] = mh + SCALE_HEIGHT;
            }
            for (var i = 0, j; (j = grid_cache[i]); ++i){
                for (var k = 0, p; (p = j[k]); ++k){
                    if(i) fillRect(ctx, p,           y[i], 1,  mh); // Freq
                    else  fillRect(ctx, SCALE_WIDTH, p,    mw, 1);  // Ampl
                }
            }
        }

        // Draw current spectrum wave in lerp
        var div_x1, div_x2; // Boundary position cache
        var gtype_ary = [{type: GTYPE_MAX, width: 2, fg: '#fc8', bg: '#733'},   // Max graph
                         {type: GTYPE_AVG, width: 2, fg: '#8cf', bg: '#337'},   // Avg graph
                         {type: GTYPE_CUR, width: 1, fg: '#6f7', bg: false}];   // Current graph
                         
        function drawCurSpectrum(peak) {
            // Assign to local vars for performance
            var ctx = ctx_wave;
            var mw  = wave_w - SCALE_WIDTH;
            var mh  = opt_freq_full ? (wave_h - SCALE_HEIGHT) / 2 | 0 : wave_h;
            var mul = mh / ampl_ary.width;
            var add = - ampl_ary.min * mul;

            // Set draw arrays for Div/Full, Cur/Max/Avg graphs
            var range_ary = [{mode: GMODE_DIV, y: wave_h - mh, h: mh}];         // Div range
            if (opt_freq_full) range_ary[1] = {mode: GMODE_FUL, y: 0, h: mh};   // Full range
            gtype_ary[0].skip = !opt_show_max;
            gtype_ary[1].skip = !opt_show_avg;
            calcLerpValAll(peak);

            // Use bevel for graph line (should be used clipping...?)
            ctx.lineJoin = 'bevel';

            // Draw spectrum graph of specified range
            range_ary.forEach(function (vr) {
                var base_h = vr.h;
                var base_y = vr.y + base_h;

                // Clear graph area
                fillRect(ctx, SCALE_WIDTH, vr.y, mw, base_h--, WAVE_AREA_COLOR);
                
                // Draw specified type of graph (Cur/Max/Avg)
                gtype_ary.forEach(function (vg) {
                    if (vg.skip) return;
                    ctx.lineWidth   = vg.width;
                    ctx.strokeStyle = vg.fg;

                    var spec = lerp_cache.dest[vr.mode][vg.type];
                    ctx.beginPath();
                    var v = base_y - getRange(spec[0] * mul + add, 1, base_h) | 0; // start point
                    ctx.moveTo(SCALE_WIDTH, v);
                    for (var x = 1; x < mw; ++x){
                        v = base_y - getRange(spec[x] * mul + add, 1, base_h) | 0;
                        ctx.lineTo(x + SCALE_WIDTH, v);
                    }
                    ctx.lineTo(SCALE_WIDTH + mw, v); // end point
                    ctx.stroke();
                    
                    // Fill for Max or Avg graph
                    if (vg.bg){
                        ctx.fillStyle = vg.bg;
                        ctx.lineTo(SCALE_WIDTH + mw, base_y);
                        ctx.lineTo(SCALE_WIDTH,      base_y);
                        ctx.fill();
                    }
                });

                // Draw peak value
                if (opt_show_peak) {
                    var pobj = lerp_cache.dest[vr.mode][GTYPE_PEAK];
                    var v = pobj.val;
                    var x = pobj.pos + SCALE_WIDTH;
                    fillRect    (ctx, x, vr.y, 1, mh, PEAK_COLOR);
                    if (x < mw / 2) fillTextLeft (ctx, v, x, vr.y + FONT_H * 2);
                    else            fillTextRight(ctx, v, x, vr.y + FONT_H * 2);
                }
            });

            drawWaveGrid(); // Pile the grid

            // Show div area by transparent color
            if(opt_freq_full){
                if (div_x1 >  0  )   fillRect(ctx, SCALE_WIDTH,          0, div_x1,      mh, WAVE_OUT_COLOR);
                if (div_x2 < mw - 1) fillRect(ctx, SCALE_WIDTH + div_x2, 0, mw - div_x2, mh, WAVE_OUT_COLOR);
            }
        }

        // Master drawing function for wave area (back ground and current spectrum)
        function drawWaveAll(){
            var MIN_STEP_FREQ = 8; // Min. px step for freq scale
            var MIN_STEP_AMPL = 4; // Min. px step for ampl scale
            
            // Clear all area at first
            var mw  = wave_w - SCALE_WIDTH;
            var mh  = wave_h;
            var ctx = ctx_wave;
            var cw = elm.idWaveCanvas.width;
            var ch = elm.idWaveCanvas.height;
            //debugLog('drawWaveAll ' + mw + ', ' + mh);
            if(audioplayer.pstate) fillRect(ctx, 0, 0, cw, ch, WAVE_AREA_COLOR);
            fillRect(ctx, 0,           0,  SCALE_WIDTH, ch,           SCALE_BG_COLOR);
            fillRect(ctx, SCALE_WIDTH, mh, mw,          SCALE_HEIGHT, SCALE_BG_COLOR);
            fillRect(ctx, wave_w,      0,  SCALE_WIDTH, ch,           SCALE_BG_COLOR);
            fillRect(ctx, wave_w,      0,  1,           ch,           SCALE_COLOR);
            grid_cache = [[],[],[]];

            // Freq axis
            fillRect    (ctx, SCALE_WIDTH - SCALE_FONT_POS, mh, wave_w, 1, SCALE_COLOR);
            fillTextLeft(ctx, '[kHz]', wave_w + SCALE_FONT_POS, ch - 4);
            drawScaleSub(ctx, 1, SCALE_WIDTH - 1, mh + 1, mw, freq_ary, MIN_STEP_FREQ);

            // Ampl scale
            fillRect     (ctx, SCALE_WIDTH - 1, 0, 1, mh + SCALE_FONT_POS);
            fillTextLeft (ctx, opt_ampl_mode? '[dB]' : '[Amp]', 0, SCALE_HEIGHT);
            if(opt_freq_full) mh = (mh - SCALE_HEIGHT) / 2 | 0;
            drawScaleSub (ctx, 0, SCALE_WIDTH - 1, mh, mh, ampl_ary, MIN_STEP_AMPL);

            // Div mode
            if (opt_freq_full){
                fillRect(ctx, SCALE_WIDTH, mh, mw, SCALE_HEIGHT, SCALE_BG_COLOR);
                // Boundary area
                var mh2 = mh + SCALE_HEIGHT;
                // Scale
                fillRect     (ctx, 0,                            mh2, SCALE_WIDTH, 1, WAVE_OUT_COLOR);
                fillRect     (ctx, SCALE_WIDTH - SCALE_FONT_POS, mh,  wave_w,      1, SCALE_COLOR);
                drawScaleSub (ctx, 2, SCALE_WIDTH - 1, mh + 1,   mw, elm.idFreqMin, MIN_STEP_FREQ);
                drawScaleSub (ctx, 0, SCALE_WIDTH - 1, mh + mh2, mh, ampl_ary,      MIN_STEP_AMPL);
                fillTextLeft(ctx, '[kHz] (full)', wave_w + 3, mh2 - 10);
            }

            // Also update grid if playback is stopped
            if(audioplayer.pstate) drawWaveGrid(); // stop or pause state

            // Calc & cache the div position
            if (opt_freq_mode) {
                var inv = 1 / Math.log(Math.pow(elm.idFreqMax.max * LOG_STAINV, 1 / mw));
                div_x1 = Math.log(freq_ary.min * LOG_STAINV + 1) * inv - 1 | 0;
                div_x2 = Math.log(freq_ary.max * LOG_STAINV + 1) * inv     | 0;
            } else {
                var scale = mw / elm.idFreqMin.max;
                div_x1 = freq_ary.min * scale - 1 | 0;
                div_x2 = freq_ary.max * scale     | 0;
            }

            // Draw selected freq range
            if (opt_freq_full){
                if (audioplayer.pstate) { // stop or pause state
                    if (div_x1 >  0)     fillRect(ctx, SCALE_WIDTH,          0, div_x1,      mh, WAVE_OUT_COLOR);
                    if (div_x2 < mw - 1) fillRect(ctx, SCALE_WIDTH + div_x2, 0, mw - div_x2, mh, WAVE_OUT_COLOR);
                }
                if (div_x1 >  0  )   fillPolygon(ctx, [SCALE_WIDTH, mh, div_x1,     0, 0, SCALE_HEIGHT], WAVE_OUT_COLOR);
                if (div_x2 < mw - 1) fillPolygon(ctx, [wave_w,      mh, div_x2 - mw,0, 0, SCALE_HEIGHT], WAVE_OUT_COLOR);
            }
            
            // Redraw current spectrum
            if (model.src) {
                drawCurSpectrum(true);
            }
        }

        ////////////////////////////////////////////////////////////////////////
        // Flow area
        var flow_next_y; // scroll border of flow-div for next drawing
        function drawTimeScale(offset, start_y, prog, invert){
            var MIN_STEP_TIME = 5; // minimum px space for time scale
            
            // Assign to local vars for performance
            var ctx         = ctx_flow;
            var fimgwidth   = elm.idFlowCanvas.width;
            var fimgheight  = elm.idFlowCanvas.height;
            var sx          = wave_w;
            var gridlen     = opt_time_grid? (fimgwidth - SCALE_WIDTH) : 0;
            var full_rewite = offset === undefined;

            // Full rewrite?
            if(full_rewite){
                offset      = start_y = 0;
                prog        = fimgheight;
                invert      = (opt_flow_mode === 2);
                flow_next_y = 0;
                pre_t_scale = audioplayer.pstate? [-1e10, -1e10] : [0,0];

                // Init flow base
                fillRect(ctx, SCALE_WIDTH,     0, sx - SCALE_WIDTH,   fimgheight, FLOW_BG_COLOR);   // spectrum area
                fillRect(ctx, sx + 1,          0, fimgwidth - sx - 1, fimgheight, SCALE_BG_COLOR);  // signal area
                fillRect(ctx, SCALE_WIDTH - 1, 0, 1,                  fimgheight, SCALE_COLOR);     // left axis
                fillRect(ctx, sx,              0, 1,                  fimgheight);                  // right axis
            }

            // Clear scale area at left side
            fillRect(ctx, 0, start_y, SCALE_WIDTH - 1, prog, SCALE_BG_COLOR);
            if (!opt_flow_mode) return; // no flow graph

            // Calc scale step
            var pxpm    = elm.idFreqMax.max * 2 * opt_flow_speed / model.fft_size / (1 - model.fft_overlap);
            var stepms  = boundsVal(MIN_STEP_TIME / pxpm);
            var keta    = getRange(6 - (stepms * 1000 + '').length, 0, 3);

            // Freq frid
            ctx.fillStyle = GRID_COLOR;
            var grid = grid_cache[1];
            for (var i = 0, p; (p = grid[i]); ++i) fillRect(ctx, p, start_y, 1, prog);

            // Draw scale and number
            ctx.fillStyle = SCALE_COLOR;
            var maxline = pre_t_scale[0];
            var maxtext = pre_t_scale[1];
            for (var cnt = offset / stepms | 0;; --cnt){
                var ms = stepms * cnt;
                var y  = (offset - ms) * pxpm | 0;
                if(y > prog + FONT_H) break;

                var y2 = start_y + (invert? prog - y - 1 : y);
                var p10 = cnt % 10;
                if(p10 < 0) p10 = -p10;
                var len = SCALE_TBL[p10];
                if(ms > maxline) { // check duplex drawing
                    if (pre_t_scale[0] < ms) pre_t_scale[0] = ms;
                    if(!p10 && gridlen) fillRect(ctx, SCALE_WIDTH, y2, gridlen, 1, GRID_COLOR); // time grid
                    fillRect(ctx, SCALE_WIDTH - 1 - len,  y2, len, 1, SCALE_COLOR);             // left scale
                    fillRect(ctx, sx,                     y2, len, 1);                          // right scale
                }
                if(!p10 && ms > maxtext && y >= FONT_H){ // Put text beyond the font height
                    if (pre_t_scale[1] < ms) pre_t_scale[1] = ms;
                    fillTextRight(ctx, msecTime(ms, keta), SCALE_WIDTH - 12, y2 + FONT_H);
                    fillTextLeft (ctx, float2str(ms / 1000, keta), sx + 12,  y2 + FONT_H);
                }
            }
            
            // Draw axis for progress area for Rewind mode
            if (invert) {
                fillRect(ctx, SCALE_WIDTH - 1, start_y, 1, prog, SCALE_COLOR);      // left axis
                fillRect(ctx, sx,              start_y, 1, prog);                   // right axis
            }
            
            // Signal border/center
            if (plugin.hide_signal) return; // hide configuration

            var numch = model.buf_nch;
            if (numch) {
                if (numch > 1) numch++;
                var s_w         = fimgwidth - sx;
                var s_w1        = s_w / numch | 0;
                var s_w2        = s_w1 / 2 | 0;
                var s_center    = sx + s_w2 + 1;
                var selch       = (model.fft_ch > numch)? 0 : model.fft_ch;
                for (var ch = 0 ; ch < numch ; ++ch){
                    var x = s_center + ch * s_w1;
                    fillRect(    ctx, x,            start_y, 1, prog, (ch === selch)? SIGSEL_CENTER_COLOR : SIGSTD_CENTER_COLOR);
                    if (ch) { // ch border
                        fillRect(ctx, x - s_w2 - 1, start_y, 1, prog, '#ccc');
                        fillRect(ctx, x - s_w2,     start_y, 1, prog, '#888');
                    }
                    if (numch > 1 && full_rewite) {
                        var size = s_w1 * 0.2 | 0;
                        fillTextCenter(ctx, ch? 'Ch:' + ch : 'Merge', x, size * 2, CH_COLOR, size + 'pt Arial');
                    }
                }
            }
        }

        // Draw flow area for spectrum of specified progress lines
        var sigmin_pre = [], sigmax_pre = []; // for connecting the signal level
        function drawFlowArea(pos, prog, stepPS, start_y, invert, cur){
            // Assign to local vars for performance
            var numch       = model.buf_nch;
            var selch       = (model.fft_ch > numch)? 0 : model.fft_ch;
            if (numch > 1) numch++; // for merge ch
            var ctx         = ctx_flow;
            var sx          = wave_w;
            var mw          = sx - SCALE_WIDTH;
            var s_w         = elm.idFlowCanvas.width - sx;
            var s_w1        = s_w / numch | 0;
            var s_w2        = s_w1 / 2 | 0;
            var s_center    = sx + s_w2 + 0.5;
            var fimgdat     = img_flow.data;
            var fimgwidth4  = img_flow.width * 4;
            var mul         = 1 / ampl_ary.width;
            var add         = - ampl_ary.min * mul;

            // Clear signal area
            fillRect(ctx, sx + 1, start_y, s_w, prog, SCALE_BG_COLOR);

            // Draw flow area by time order
            for (var y = prog; y--; ++pos){
                var y2 = invert? prog - 1 - y : y;
                var addr = y2 * fimgwidth4;

                // calc lerp spectrum (Cur/Div only)
                var curpos  = pos    * stepPS | 0;
                var nextpos = curpos + stepPS | 0;
                if (!model.transAll(curpos)) return false;
                var spec = calcLerpSpec(model.spec_low, GMODE_DIV, GTYPE_CUR);

                // Put pixel of spectrum flow
                for (var x = 0; x < mw; ++x){
                    var col = opt_pal.color(spec[x] * mul + add);
                    fimgdat[addr++] = col[0];
                    fimgdat[addr++] = col[1];
                    fimgdat[addr++] = col[2];
                    fimgdat[addr++] = 255;
                }

                // Draw signal level for each channels to right side
                y2 += start_y;
                if (!plugin.hide_signal) {
                    for (var ch = 0 ; ch < numch ; ++ch){
                        var dat = model.srcbuf(curpos, nextpos, ch);
                        if (!dat) break;
                        var sigmin = dat[0];
                        var sigmax = dat[0];
                        for (var i = nextpos - curpos; --i; ){
                            var sigval = dat[i];
                            if(sigmin > sigval) sigmin = sigval;
                            if(sigmax < sigval) sigmax = sigval;
                        }
                        sigmin *= s_w2; // keep float (for transparent terminal)
                        sigmax *= s_w2; // keep float (for transparent terminal)
                        var cx1 = (sigmin >= sigmax_pre[ch])? sigmax_pre[ch] - 1 : sigmin;
                        var cx2 = (sigmax <= sigmin_pre[ch])? sigmin_pre[ch] + 1 : sigmax;
                        fillRect(ctx, s_center + ch * s_w1 + cx1, y2, cx2 - cx1 + 1, 1, (ch === selch)? SIGSEL_COLOR : SIGSTD_COLOR);
                        sigmin_pre[ch] = sigmin;
                        sigmax_pre[ch] = sigmax;
                    }
                }
                
                if (plugin.draw) plugin.draw(y2, invert);
            }

            // Put flow image of prog-length to ctx
            ctx.putImageData(img_flow, SCALE_WIDTH, start_y, 0, 0, mw, prog);
            
            // Also draw time scale of prog-length
            drawTimeScale(cur, start_y, prog, invert);
        }

        // Draw Spectrum graph/Flow of delta step
        function drawDelta(cur, pre){
            //console.log('drawDelta: ' + msecTime(pre, 3) + ' - ' + msecTime(cur, 3));

            // Check the progress time of sampling unit
            var mSR         = model.buf_sr / 1000;  // sample/msec
            var cur_offset  = cur * mSR;
            var pre_offset  = pre * mSR;
            if (cur_offset - pre_offset < 1) return 0; // progress < 1 sample unit

            // Assign to local vars for performance
            var fimgwidth   = img_flow.width;
            var fimgheight  = img_flow.height;
            var ctx         = ctx_flow;

            // Check the progress step of flow line
            var step    = model.fft_step;
            var stepPS  = step / opt_flow_speed;
            var pre_pos = (pre < 0)? 0 : (pre_offset / stepPS + 1 | 0);
            var cur_pos =                 cur_offset / stepPS + 1 | 0;
            var prog    = cur_pos - pre_pos;
            

            // Draw dlow area
            if (prog){
                // Branch by each flow mode (Enable/Disable)
                if(opt_flow_mode){
                    var scroll = opt_flow_mode === 1; // Roll/Over
                    // prog is larger than height of flow area?
                    if (prog > fimgheight){
                        // Skip to current position (All rewrite)
                        pre_pos = cur_pos - fimgheight;
                        prog = fimgheight;
                        if (!scroll) flow_next_y = 0; // reset start position
                    } else {
                        // scroll the last flow image
                        if (scroll) ctx.drawImage(elm.idFlowCanvas, 0, prog);

                        // Draw border if specified
                        if(flow_border){
                            fillRect(ctx, 0, scroll? prog : (flow_next_y - flow_border), img_flow.width, flow_border, FLOW_BORDER_COLOR[flow_border - 1]);
                            flow_border = 0;
                        }
                    }
                    // Branch by each flow mode (Scroll/Rewind)
                    if (scroll) {
                        // Scroll
                        drawFlowArea(pre_pos, prog, stepPS, 0, false, cur);
                    } else {
                        // Rewind
                        var prog1 = fimgheight - flow_next_y; // Left height
                        if (prog1 < prog){ // Divide the flow for rewind
                            drawFlowArea(pre_pos, prog1, stepPS, flow_next_y, true, cur);
                            flow_next_y = 0;
                            pre_pos += prog1;
                            prog    -= prog1;
                        }
                        drawFlowArea(pre_pos, prog, stepPS, flow_next_y, true, cur);
                        flow_next_y = (flow_next_y + prog) % fimgheight;

                        // Progress border
                        fillRect(ctx, 0, flow_next_y    , fimgwidth, 1, '#fff');
                        fillRect(ctx, 0, flow_next_y + 1, fimgwidth, 1, '#000');
                    }
                } else { // No flow
                    // Perform FFT to current offset for statistics (Max/Avg)
                    if (!model.transAll(cur_offset)) return false;
                }
            } else if (!opt_no_overlap) {
                return 0;
            } else {
                if (!model.transLow(cur_offset)) return false; // Calc spectrum at realtime position (ignore overlap)
            }

            // Draw wave area
            var tick = Date.now(); // Use real time
            if (tick - peak_prems > opt_peak_period) peak_prems = tick; // Update the peak
            else tick = false;
            drawCurSpectrum(tick);
            return prog;
        }

        // FPS debug //////////////////////////////////////////////////////////////////
        var FPS_INTERVAL = 1000;
        var fps_cnt = 0;
        var fps_ms  = 0;
        var fps_msg = '';

        function drawFPS(){
            var curms = Date.now();
            if (!fps_ms) fps_ms = curms;
            ++fps_cnt;
            var diff = curms - fps_ms;
            if (diff > FPS_INTERVAL){
                fps_msg = 'FPS:' + float2str(fps_cnt * 1000 / diff, 1);
                fillRect    (ctx_wave,           wave_w + 4,  2, 45, 16, '#080');
                fillTextLeft(ctx_wave, fps_msg, wave_w + 6, 14,         '#eee');
                fps_ms = curms;
                fps_cnt = 0;
            }
        }

        // Tool tips object ////////////////////////////////////////////////////
        var tooltip = (function() {
            var TIP_TIMEOUT = 700;  // ms
            var tip_start = 0;
            var tip_timer = null;

            // Hide tips at end of timeout
            function setHideTimer(ms){
                if (tip_timer) clearTimeout(tip_timer);
                tip_timer = ms? setTimeout(hide, ms + 1) : null;
            }
            function hide(){
                var dif = TIP_TIMEOUT - (Date.now() - tip_start);
                if (dif > 0){
                    setHideTimer(dif);
                } else {
                    elm.idTipDiv.style.display = 'none'; // hide
                    setHideTimer(false);
                }
            }
            
            // Show one tips at specified position with auto-hide switch
            function show(x, y, shift, msg, autohide){
                // Check windows range
                elm.idTipDiv.innerHTML = msg;
                var w       = elm.idDropDiv.offsetWidth;
                var h       = elm.idDropDiv.offsetHeight;
                var tip     = elm.idTipDiv.style;

                // Move tips to fix the root window
                if(x < 200)         { tip.left  = x + shift + 'px'; tip.right   = '';                  }
                else                { tip.left  = '';               tip.right   = w - x + shift + 'px';}
                if(y < shift + 20)  { tip.top   = y + shift + 'px'; tip.bottom  = '';                  }
                else                { tip.top   = '';               tip.bottom  = h - y + shift + 'px';}

                // Show tips and set auto hide timer
                tip.display = 'block';
                tip_start   = Date.now();
                setHideTimer(autohide && TIP_TIMEOUT);
            }

            // public method
            return {
                hide: hide,
                show: show,
            };
        })();

        // Control dialog box
        function showDialog(item, show){
            item.style.display = (show === false)? 'none' : 'block';
        }

        // Control config sub menu
        function toggleConfBox(item){
            //item.hidden= !item.hidden; // item.hidden can't use on inline-block, so use display style for hide.
            item.style.display = item.offsetHeight? 'none' : 'inline-block'; // As default, display is '', so check by offsetHight
        }

        ////////////////////////////////////////////////////////////////////////
        // Resizing
        var resize_param = [];
        var resize_timer;
        var resize_manual; // for Opera browser
        function resizeAll(e) {
            // For browser window resizing, pending the multiple events, and resize at last event.
            if(e){
                if (resize_timer) clearTimeout(resize_timer);
                resize_timer = setTimeout(resizeAll, 500);
                debugLog('Pending resize');
                return;
            }
            resize_timer = 0;

            // Check changes
            var cur = [elm.idDropDiv.offsetWidth - elm.idConfDiv.offsetWidth, elm.idDropDiv.offsetHeight- elm.idWaveDiv.offsetHeight];
            if (arrayComp(cur, resize_param)) return; // Not cheched
            resize_param = cur;
            debugLog('Resize (' + cur + ')');

            // Fit DIVs (of canvas) for full screen
            elm.idViewDiv.style.width  = cur[0] + 'px';
            elm.idFlowDiv.style.height = cur[1] + 'px';
            
            // Opera browser can't use box arrangement...?
            if (elm.idViewDiv.offsetTop !== 0 || resize_manual) {
                // Manual arrangement for Opera browser
                resize_manual = true;
                elm.idViewDiv.style.position= 'absolute';
                elm.idViewDiv.style.top     = '0px';
                elm.idViewDiv.style.left    = elm.idConfDiv.offsetWidth + 'px';
            }
            
            // Fit canvas size for full screen
            var BORDERSIZE = 2; //TODO from CSS...?
            elm.idWaveCanvas.width  = elm.idWaveDiv.offsetWidth - 10  - BORDERSIZE;
            elm.idWaveCanvas.height = elm.idWaveDiv.offsetHeight      - BORDERSIZE;
            elm.idFlowCanvas.width  = elm.idFlowDiv.offsetWidth       - BORDERSIZE;
            elm.idFlowCanvas.height = elm.idFlowDiv.offsetHeight      - BORDERSIZE;
            elm.idColorCanvas.width = elm.idColorDiv.offsetWidth * COLORBAR_SCALE | 0;
            
            // Pre-calc useful vars
            wave_w  = elm.idWaveDiv.offsetWidth * 0.8 | 0;
            wave_h  = elm.idWaveCanvas.height - SCALE_HEIGHT;
            wave_wR = 1 / (wave_w - SCALE_WIDTH);
            flow_next_y = 0; // reset border line

            // For pixel drawing
            img_flow = ctx_flow.createImageData(elm.idFlowCanvas.width, elm.idFlowCanvas.height);

            // Force redraw by new size
            update({resize: true});
        }

        ///////////////////////////////////////////////////////////////////////////////
        // Redraw funcs
        ///////////////////////////////////////////////////////////////////////////////
        var udflag = {};
        var auto_redraw = false;

        // Redraw func table for each drawing area
        var REDRAW_FUNC = [
            ['wave',    drawWaveAll],
            ['flow',    function() { flow_border = 1; if(audioplayer.pstate) drawTimeScale(); }],
            ['flow2',   drawTimeScale],
            ['color',   drawColorBar],
            ['block',   function() { elm.idFFTSel.value = model.fft_size; }],
            ['overlap', function() { elm.idOverlapText.innerText = Math.round(model.fft_overlap * 100) + '%'; }],
            ['ch',      function() { if(model.fft_ch > model.buf_nch) elm.idChAll.selected = true; }],
            ['pbs',     function() { elm.idPBSText.innerText = (audioplayer.speed * 100 | 0) + '%'; }],
            ['volume',  function() { elm.idVolumeText.innerText = audioplayer.volume? ((audioplayer.volume * 100 | 0) + '%') : 'Mute'; }],
        ];
        function redraw(f) {
            // Check flag of redraw
            if (f === false) {
                auto_redraw = false;
                return; // skip redraw
            } else  if (f === true) {
                auto_redraw = true;
                // no return
            } else if (f !== undefined) {
                update(f);
            }

            //var uplist = " Draw: ";
            REDRAW_FUNC.forEach(function(v) {
                if (udflag[v[0]]) {
                    //uplist += v[0] + " ";
                    udflag[v[0]] = false;
                    v[1]();
                }
            });
            //console.log(uplist);
        }
        
        var UPDATE_MAP = {
            // update event:    [REDRAW_FUNC targets]

            // From model
            'fft_src':          ['wave',    'flow'],
            'fft_block_size':   ['wave',    'flow ',    'block'     ],
            'fft_ch':           ['wave',    'flow ',    'ch'        ],
            'fft_window':       ['wave',    'flow '                 ],
            'fft_overlap':      [           'flow ',    'overlap'   ],
            'fft_maxavg':       ['wave',                            ],
            
            // From view (self)
            'freq_range':       ['wave',    'flow'                  ],
            'freq_mode':        ['wave',    'flow'                  ],
            'freq_full':        ['wave',    'flow'                  ],
            'freq_grid':        ['wave',    'flow'                  ],
            'time_grid':        [           'flow'                  ],
            'ampl_grid':        ['wave',                            ],
            'ampl_range':       ['wave',    'flow',     'color'     ],
            'flow_mode':        [           'flow2'                 ],
            'fds':              [           'flow2'                 ],
            'flow_fix':         [           'flow'                  ],
            'pbs':              [                       'pbs'       ],
            'volume':           [                       'volume'    ],
            'colorbar':         [           'flow',     'color'     ],
            'fps':              ['wave',                            ],
            'lerp':             ['wave',    'flow'                  ],
            'no_overlap':       ['wave'                             ],
            'showmax':          ['wave'                             ],
            'showavg':          ['wave'                             ],
            'showpeak':         ['wave'                             ],
            'resize':           ['wave',    'flow2',    'color'     ],
        };

        function set_udflag (v) {
             udflag[v] = true;
        }
        // Update notification
        function update(f) {
            for (var n in f) {
                // Check the redraw targets from specified update event
                var draws = UPDATE_MAP[n];
                if (draws) {
                    //console.log('update: ', n, draws);
                    draws.forEach(set_udflag);
                }
                
                // notification chain for plugin
                var cb = plugin[n];
                if (cb && cb() === false) { // if method is exist and return false, unload this plugin.
                    var deinit = plugin.deinit;
                    plugin = {};
                    if (deinit) deinit();
                    elm.idPluginNone.checked = true;
                }
            }
            
            // Redraw now if auto_redraw is set
            if (auto_redraw) redraw();
        }

        ///////////////////////////////////////////////////////////////////////////////
        // Start playback
        function start() {
            // Init playback related parameters if stopped
            if(audioplayer.pstate === 1) {
                flow_border = 2;
                peak_prems  = 0;
                pre_t_scale = [0,0];
            }

            audioplayer.play(audioplayer.pstate === 1);
        }
        

        ///////////////////////////////////////////////////////////////////////////////
        // On screen debug print (for non-console environment, e.g. android/iPad, etc)
        ///////////////////////////////////////////////////////////////////////////////
        var dbg_start;
        var dbg_count = 0;
        function debugLog(msg){
            if (!debug_OSD) return;
            var cur = Date.now();
            if (!dbg_start) dbg_start = cur; // cur > 0
            msg = ++dbg_count + ' (' + msecTime(cur - dbg_start, 3) + ') ' +msg;
            console.log(msg); // It's enough for debug if we use a PC...
            
            // Show debug in overlaied DIV
            if (elm.idDebugDiv.innerText) {
                var srcText = elm.idDebugDiv.innerText;
                elm.idDebugDiv.innerText = srcText.substr((dbg_count > 30)? srcText.search('\n')   + 1 : 0) + '\n'   + msg;
            } else {
                // Firefox cannot use innerText ...!?
                var srcHTML = elm.idDebugDiv.innerHTML;
                elm.idDebugDiv.innerHTML = srcHTML.substr((dbg_count > 30)? srcHTML.search('<br>') + 4 : 0) + '<br>' + msg;
            }
        }

        // Set input source information
        function setInfo(info) {
            elm.idInputCh.innerText = model.buf_nch + 'ch';
            elm.idInputSr.innerText = model.buf_sr  + 'Hz';
            elm.idInputBs.innerText = model.buf_bit + 'bit';
            elm.idInputDr.innerText = model.buf_dur? msecTime(model.buf_dur * 1000, 3) + ((model.buf_dur < 60)? 's' : '') : '-----';
            elm.idInputNm.value     = info;
            elm.idSrcTable.title    = 'Source: ' + info; // Title may be forced out, so add the popup

            // For title bar of browser
            document.getElementById('idTitle').innerText = 'SpeAnaWeb: ' + info;
        }

        ///////////////////////////////////////////////////////////////////////////////
        // Initialize (onload)
        ///////////////////////////////////////////////////////////////////////////////
        function init() {
            // Pre-load all DOM elements to elm object which has 'idXXX'.
            var elms = document.body.getElementsByTagName('*');
            for(var i = 0, j; (j = elms[i]); ++i) {
                if(j.id.substr(0,2) === 'id') {
                    elm[j.id] = j;
                }
            }

            // Cache context of canvas
            ctx_flow  = elm.idFlowCanvas .getContext('2d');
            ctx_wave  = elm.idWaveCanvas .getContext('2d');
            ctx_color = elm.idColorCanvas.getContext('2d');

            // Init view config by default value on HTML
            opt_ampl_mode = elm.idAmpldB.checked? 1 : 0;
            changeFreqRange(3);
            changeAmplRange(3);
            changeFlowMode();
            changeColor         (elm.idColorSel.value, elm.idPalInvert.checked);
            changeFDS2          (elm.idFDSRange.value);
            changePlaybackSpeed (elm.idPBSRange.value);
            changeVolume        (elm.idVolume.value);
            changeFreqGrid      (elm.idFreqGrid.checked);
            changeAmplGrid      (elm.idAmplGrid.checked);
            changeTimeGrid      (elm.idTimeGrid.checked);
            changeLerp          (elm.idLerp.checked);
            changeNoOverlap     (elm.idCurNoOL.checked);
            changeWaveMax       (elm.idWaveMax.checked);
            changeWaveAvg       (elm.idWaveAvg.checked);
            changeWavePeak      (elm.idWavePeak.checked);
            changePeakPeriod    (elm.idPeakPeriod.value);
            changeOLDebug       (elm.idOLDebug.checked);
            changeFpsDebug      (elm.idFpsDebug.checked);

            // for model change
            model.setObserver(update);
        }
        
        // public method of view
        return {
            init:               init,

            // config (TODO getter/setter...)
            changeLerp:         changeLerp,
            changeNoOverlap:    changeNoOverlap,
            changeWaveMax:      changeWaveMax,
            changeWaveAvg:      changeWaveAvg,
            changeWavePeak:     changeWavePeak,
            changePeakPeriod:   changePeakPeriod,

            changePlaybackSpeed:changePlaybackSpeed,
            changeVolume:       changeVolume,
            changeColor:        changeColor,
            
            changeFreqMode:     changeFreqMode,
            changeFreqRange:    changeFreqRange,
            changeFreqFull:     changeFreqFull,
            changeFreqGrid:     changeFreqGrid,
            changeAmplGrid:     changeAmplGrid,
            changeTimeGrid:     changeTimeGrid,
            changeFlowMode:     changeFlowMode,
            changeAmplMode:     changeAmplMode,
            changeAmplRange:    changeAmplRange,
            changeFDS2:         changeFDS2,
            changeOLDebug:      changeOLDebug,
            changeFpsDebug:     changeFpsDebug,
            
            // drawing
            drawColorBar:       drawColorBar,
            drawFPS:            drawFPS,
            resizeAll:          resizeAll,
            get ctx_flow()      { return ctx_flow; },
            get ctx_wave()      { return ctx_wave; },

            // view config
            get ampl_mode()     { return opt_ampl_mode; },
            get ampl_ary()      { return ampl_ary; },
            get freq_width()    { return freq_ary.width; },
            get flow_speed()    { return opt_flow_speed; },
            set flow_speed(v)   { changeFDS(v); },
            
            get wave_w()        { return wave_w; },
            get wave_wR()       { return wave_wR; },
            get scale_w()       { return SCALE_WIDTH; },
            get freq_mode()     { return opt_freq_mode; },
            get div_half()      { return (div_x1 + div_x2) / 2; },
            
            // Tool tips
            showTip:            tooltip.show,
            hideTip:            tooltip.hide,
            
            showDialog:         showDialog,
            toggleConfBox:      toggleConfBox,
            
            // Audio presentation is also view
            setSrc:             audioplayer.setSrc,
            setInfo:            setInfo,
            start:              start,
            stop:               audioplayer.stop,
            pause:              audioplayer.pause,
            get pstate()        { return audioplayer.pstate; },
            get volume()        { return audioplayer.volume; },
            
            // Update notification
            update:             update,
            redraw:             redraw,

            debugLog:           debugLog,
        };
    })();


    ////////////////////////////////////////////////////////////////////////////
    // Controller Object
    ////////////////////////////////////////////////////////////////////////////
    var controller = (function () {
        var touch_dev; // true: touch panel device mode (others: mouse mode)

        ////////////////////////////////////////////////////////////////////////
        // Mouse/Touch control object
        ////////////////////////////////////////////////////////////////////////
        var mouse = (function(){
            // mouse control parameters
            var m_mode;
            var m_base;
            var m_scale;

            // for offset coord of element
            var m_off_x = 0;
            var m_off_y = 0;

            // Get mouse position
            function getX() { return event.touches? event.targetTouches[0].clientX : event.clientX; }
            function getY() { return event.touches? event.targetTouches[0].clientY : event.clientY; }

            function offX(){
                var x = getX();
                if(event.type === 'touchstart' || event.type === 'mousedown') m_off_x = event.target.getBoundingClientRect().left;
                return x - m_off_x;
            }

            function offY(){
                var y = getY();
                if(event.type === 'touchstart' || event.type === 'mousedown') m_off_y = event.target.getBoundingClientRect().top;
                return y - m_off_y;
            }

            // set tooltips at mouse position
            function setTip(msg, autohide) {
                view.showTip(getX(), getY(), touch_dev? 30 : 4, msg, autohide); // Consider the visibility of finger operation
            }

            // enter mouse capture mode
            function enterMode(type, cursor, fnUp, fnMove){
                m_mode = type;

                // Event registration is needed for first time only, but...
                if (touch_dev){
                    var div = event.target;
                    div.ontouchend = fnUp;
                    div.touchcancel= fnUp; // This event will (may) be occurred at phone-call
                    div.ontouchmove= fnMove;
                } else {
                    // I'd like to use SetCapture, but that is for IE only. So, use manual Capture-Div.
                    var capDiv = elm.idCaptureDiv;
                    capDiv.onmouseup      = fnUp;
                    capDiv.onmouseout     = fnUp;
                    capDiv.onmousemove    = fnMove;
                    capDiv.style.display  = 'block';
                    capDiv.style.cursor   = cursor;

                    // prevent changing the mouse cursor
                    event.preventDefault();
                }

                // set first position (for guide-bar)
                fnMove();
            }

            // leave ouse capture mode
            function leaveMode(){
                m_mode = 0;
                if (!touch_dev){
                    // Disable the mouse capture div (for prevent more mouseup/mouseout event)
                    var capDiv = elm.idCaptureDiv;
                    capDiv.onmouseout = capDiv.onmouseup = capDiv.onmousemove = '';
                    capDiv.style.display = 'none';
                
                }
                view.hideTip();
            }

            // Check multi touch state (return 0 at mouse event)
            function multiTouch(){
                return event.touches? event.touches.length : 0;
            }

            // prevent default at single touch only
            function preventSingle(){
                if (multiTouch() < 2 && event.type !== 'touchstart') event.preventDefault();
            }

            // COLOR: Chane ampl range (color palette) by mouse ////////////////
            var MTYPE_AMPL_MIN = 1;
            var MTYPE_AMPL_MAX = 2;

            // Select min or max from click coord for change
            function colorDown(){
                debugLog('colorDown mt=' + multiTouch() + ' e=' + event.type);
                if (m_mode || multiTouch() > 1) return; // Skip at Multi touch

                // set move parameters
                m_scale = (elm.idAmplMin.min - elm.idAmplMax.max) / elm.idColorCanvas.width; // Negative value is useful for number calculation, later...
                enterMode((elm.idAmplMin.min - offX() * m_scale < (+elm.idAmplMax.value + (+elm.idAmplMin.value)) / 2)? MTYPE_AMPL_MIN : MTYPE_AMPL_MAX, 'col-resize', colorUp, colorMove);
            }

            // Fix changing by last value
            function colorUp(){
                debugLog('colorUp mt=' + multiTouch() + ' e=' + event.type);
                if (multiTouch() > 0) return; // Other fingers still remain
                leaveMode();
                view.drawColorBar(); // erase guide-bar
            }

            // Re-adjust range value by a moving position
            function colorMove(){
                var x = offX();
                debugLog('colorMove mt=' + multiTouch() + ' e=' + event.type + ' x=' + x);

                var target = (m_mode === MTYPE_AMPL_MIN)? [elm.idAmplMin, 'Min. '] : [elm.idAmplMax, 'Max. '];
                target[0].value = elm.idAmplMin.min - x * m_scale;
                view.changeAmplRange(m_mode, false, x);
                setTip(target[1] + target[0].value + (view.ampl_mode? 'dB' : ''));
                preventSingle();
            }

            // Parallel displacement the ampl range
            function colorWheel(){
                debugLog('colorWheel delta=' + event.wheelDelta + ' e=' + event.type);
                elm.idAmplMin.value -= event.wheelDelta / 24 * elm.idAmplMin.step;
                view.changeAmplRange(1, true);
                setTip(elm.idAmplMin.value + ' - ' + elm.idAmplMax.value + (view.ampl_mode? 'dB' : ''), true);
                event.preventDefault();
            }

            // WAVE: Chane freq range by mouse /////////////////////////////////
            var MTYPE_FREQ_MIN  = 1;
            var MTYPE_FREQ_MAX  = 2;
            var MTYPE_FREQ_SLIDE= 3;

            // Select change type (min/max/slice) by the click position
            function waveDown(){
                debugLog('waveDown mt=' + multiTouch() + ' e=' + event.type);
                if (m_mode || multiTouch() > 1) return; // Skip at Multi touch

                // Set change type
                if (elm.idFreqFull.disabled || !elm.idFreqFull.checked || offY() < elm.idWaveCanvas.height / 2){
                    // Change min or max
                    view.changeFreqFull(-1); // force freq full
                    m_base  = elm.idFreqMax.max - elm.idFreqMin.min;
                    m_scale = (m_base) * view.wave_wR;
                    if (view.freq_mode) m_base  = Math.pow(m_base * LOG_STAINV, view.wave_wR);
                    enterMode((offX() - view.scale_w < view.div_half)? MTYPE_FREQ_MIN : MTYPE_FREQ_MAX, 'col-resize', waveUp, waveMove);
                } else {
                    // change by slide (both min/max)
                    m_scale = (elm.idFreqMin.value - elm.idFreqMax.value) * view.wave_wR; // Negative value is useful for number calculation, later...
                    m_base  = offX() * m_scale - elm.idFreqMin.value;
                    enterMode(MTYPE_FREQ_SLIDE, 'e-resize', waveUp, waveMove);
                }
            }

            // Fix changing by last value
            function waveUp(){
                debugLog('waveUp mt=' + multiTouch() + ' e=' + event.type);
                if (multiTouch() > 0) return; // Other fingers still remain

                if (m_mode !== MTYPE_FREQ_SLIDE)  view.changeFreqFull(-1); // force freq full
                leaveMode();
                view.changeFreqRange(3); // erase guide-bar
            }

            // Re-adjust range value by a moving position
            function waveMove(){
                var x = offX();
                if(m_mode === MTYPE_FREQ_SLIDE) {
                    var val = x * m_scale - m_base;
                    elm.idFreqMin.value = val;
                    view.changeFreqRange(1, true, view.pstate && x, val < 0 || elm.idFreqMax.max - view.freq_width < val);
                    setTip(elm.idFreqMin.value + 'kHz - ' + elm.idFreqMax.value + 'kHz');
                } else {
                    var TARGET_LIST = [[elm.idFreqMin, 'Min. '], [elm.idFreqMax, 'Max. ']];
                    var target = TARGET_LIST[m_mode - MTYPE_FREQ_MIN];
                    var x2 = x - view.scale_w;
                    target[0].value = ((view.freq_mode? Math.pow(m_base, x2) * LOG_START : x2 * m_scale) * 100 | 0) / 100; // cur to x.xx kHz
                    view.changeFreqRange(m_mode, false, view.pstate && x, x < view.scale_w || view.wave_w < x);
                    setTip(target[1] + target[0].value + 'kHz');
                }
                debugLog('waveMove mt=' + multiTouch() + ' e=' + event.type + ' x=' + x + ' m=' + m_mode);
                preventSingle();
            }

            // Parallel displacement the freq range
            function waveWheel(){
                debugLog('waveWheel delta=' + event.wheelDelta + ' e=' + event.type);
                elm.idFreqMin.value -= event.wheelDelta / 6 * elm.idFreqMin.step;
                view.changeFreqRange(1, true);
                setTip(elm.idFreqMin.value + 'kHz - ' + elm.idFreqMax.value + 'kHz', true);
                event.preventDefault();
            }

            // FLOW: Chane flow speed or FFT ch by mouse ///////////////////////
            var MTYPE_FLOW_CHANGE = 1;
            var MTYPE_SEL_CHANNEL = 2;

            // Set flow speed or FFT channel by relative coord
            function flowDown(){
                debugLog('flowDown mt=' + multiTouch() + ' e=' + event.type);
                if (m_mode || multiTouch() > 1) return;// Skip at Multi touch

                // Select change target by X coord
                var chnum = model.buf_nch;
                var x = offX();
                if (x < view.wave_w || chnum < 2){ // Change flow speed
                    m_base   = offY();
                    m_scale = elm.idFDSRange.value;
                    enterMode(MTYPE_FLOW_CHANGE, 'row-resize', flowUp, flowMove_spd);
                } else {    // Change FFT ch
                    enterMode(MTYPE_SEL_CHANNEL, 'col-resize', flowUp, flowMove_ch);
                }
            }

            // Fix changing by last value
            function flowUp(){
                debugLog('flowUp mt=' + multiTouch() + ' e=' + event.type);
                if (multiTouch() > 0) return; // Other fingers still remain
                leaveMode();
                view.update({flow_fix: true});
            }

            // Change flow speed by relative coord of Y
            function flowMove_spd(){
                var y = offY();
                debugLog('flowMove_spd mt=' + multiTouch() + ' e=' + event.type + ' y=' + y);

                // Change speed by nearest integer value
                var cand = m_scale - (m_base - y) / elm.idFlowCanvas.height * 20 | 0;
                var next = getRange(cand, elm.idFDSRange.min, elm.idFDSRange.max);
                elm.idFDSRange.value = next;
                view.changeFDS2(next, view.pstate && y, cand === next);
                setTip('Flow speed: ' + elm.idFDSText.innerText);
                preventSingle();
            }

            // Select FFT ch by X coord
            function flowMove_ch(){
                var flowW = view.wave_w;
                var num = model.buf_nch + 1;
                var ch = getRange((offX() - flowW) / (elm.idFlowCanvas.width - flowW) * num | 0, 0, num - 1);
                elm.idFFTCh.value = ch;
                model.fft_ch = ch;
                setTip('Channel: ' + elm.idFFTCh.item(ch).innerHTML);
            }

            // Change flow spped or FFT ch by wheel step
            function flowWheel(){
                debugLog('flowWheel delta=' + event.wheelDelta + ' e=' + event.type);

                var chnum = model.buf_nch;
                var x = offX();
                if (x < view.wave_w || chnum < 2){ // Change flow speed
                    elm.idFDSRange.value = getRange(elm.idFDSRange.value - event.wheelDelta / 120, elm.idFDSRange.min, elm.idFDSRange.max);
                    view.changeFDS2(elm.idFDSRange.value);
                    setTip('Flow speed: ' + elm.idFDSText.innerText, true);
                } else { // Change FFT ch
                    var ch = (elm.idFFTCh.value - event.wheelDelta / 120 + chnum + 1) % (chnum + 1);
                    elm.idFFTCh.value = ch;
                    model.fft_ch = ch;
                    setTip('Channel: ' + elm.idFFTCh.item(ch).innerHTML, true);
                }
                event.preventDefault();
            }

            // public method
            return {
                colorDown:  colorDown,
                waveDown:   waveDown,
                flowDown:   flowDown,
                colorWheel: colorWheel,
                waveWheel:  waveWheel,
                flowWheel:  flowWheel,
            };
        })();
        
        ////////////////////////////////////////////////////////////////////////
        // Sound decoder
        ////////////////////////////////////////////////////////////////////////
        function changeAudioBufCompleteCheck(){
            if (elm.idAudio.readyState === elm.idAudio.HAVE_ENOUGH_DATA) {
                view.showDialog(elm.idDecodeDialog, false);
                elm.idDropDiv.style.cursor = '';
                //setTimeout(view.play, 500);
                return;
            }
            setTimeout(changeAudioBufCompleteCheck, 500);
        }

        // Change audio buffer
        var oldSR;
        function changeAudioBuf(buf, src, info){
            // Freq range (min/max) also scaleing by the same ratio by current settings
            if (!oldSR) oldSR = model.buf_sr; // init
            if(oldSR !== buf.sampleRate){
                elm.idFreqMin.max = elm.idFreqMax.max = buf.sampleRate / 2000; // Unit: KHz
                if (oldSR){ // value also adjust by linar scaleing
                    var ratio = buf.sampleRate / oldSR;
                    elm.idFreqMin.value *= ratio;
                    elm.idFreqMax.value *= ratio;
                }
                view.changeFreqRange(3);
                elm.idStart.disabled = false;
                oldSR = buf.sampleRate;
            }
            model.src = buf;
            view.setSrc(src);
            view.setInfo(info);

            // Hide invalid channel from pull down menu
            var ID_CHANNEL_LIST = [elm.idCh1, elm.idCh2, elm.idCh3, elm.idCh4, elm.idCh5, elm.idCh6];
            var maxch = buf.numberOfChannels;
            for (var i = 0, j; (j = ID_CHANNEL_LIST[i]); ++i) {
                j.disabled = i >= maxch;
                // Select merge channel if invalid channel is specified
                if (i >= maxch && j.selected) elm.idChAll.selected = true;
            }

            //if (elm.idAudio) {
            if (false) {
                // buffer wait
                setTimeout(changeAudioBufCompleteCheck, 500);
            } else {
                // Hide the wait dialog and curspr
                view.showDialog(elm.idDecodeDialog, false);
                elm.idDropDiv.style.cursor = '';
                
                // For automatic play
                //setTimeout(view.play, 500);
            }
        }

        // Decode sound using decodeAudioData of audio_ctx or original WAV decoder
        function decodeAudioBuf(v, src, info){
            // There is no progress callback on decodeAudioData, so use just wait cursor!
            elm.idDropDiv.style.cursor = 'wait'; // Not whole area...
            view.showDialog(elm.idDecodeDialog);
            
            if (audio_ctx && info.substr(-4).toLowerCase() !== '.wav') {
                // Use audio_ctx for decode
                audio_ctx.decodeAudioData(v, 
                    function(buf){ // Success of decoding
                        changeAudioBuf(buf, src, info);
                    },
                    function(){ // onerror  (There is some kind of MP3 format file which makes error by decodeAudioData...)
                        alert('Cannot decode audio data');
                        view.showDialog(elm.idDecodeDialog, false);
                        elm.idDropDiv.style.cursor = '';
                    });
            } else {
                // Use original WAV decoder for WAV (or Web Audio API is not useful)
                var buf = WaveDecoder.decode(v, info);
                if (buf.error){
                    view.showDialog(elm.idDecodeDialog, false);
                    elm.idDropDiv.style.cursor = '';
                    alert(buf.error);
                } else {
                    // Success of decoding
                    changeAudioBuf(buf, src, info + ' (' + buf.bits + 'bit)'); // This decoder also has bits info
                }
            }
        }

        // Open Local sound file
        function loadLocalFile(file){
            var fr = new FileReader();
            fr.onload = function(event) {
                view.stop(); // Stop current playback
                decodeAudioBuf(event.target.result, URL.createObjectURL(file), file.name);
            };
            fr.onerror = function() { alert('Cannot open file:' + file.name); };
            fr.readAsArrayBuffer(file);
        }

        // Open Local microphone device (T.B.D.)
        /*
        function openMic(){
            // Read sound stream from microphone
            navigator.getUserMedia({audio: true}, function() {
                alert('Not implemented...');
                // In future...
                //var mic = audio_ctx.createMediaStreamSource(stream);
                //var filter = audio_ctx.createBiquadFilter();

                // microphone -> filter -> destination.
                //mic.connect(filter);
                //filter.connect(audio_ctx.destination);

                //elm.idAudio.src = window.URL.createObjectURL(stream);
                //elm.idVideo.src = window.URL.createObjectURL(stream);
            }, function(e){
                alert('getUserMedia failed ' + e);
            });
        }
        */

        // File select and preventDefault
        function selFile(files, pd){
            if (files.length > 0) loadLocalFile(files[0]);
            if(pd) event.preventDefault();
        }
        function downloadFile() {
            // Download sound file from WEB via XHR
            elm.idDownloadStart.disabled = true;
            elm.idProgressBar.innerText = 'Start download...';

            // Download using HTTP
            var url = elm.idSrcHttpUrl.value;
            var xhr = new XMLHttpRequest();
            xhr.open('GET', url, true);
            xhr.responseType = 'arraybuffer';
            var onloadend   = function() { elm.idProgressBar.innerText = ''; elm.idDownloadStart.disabled = false; };
            xhr.onload      = function() { view.showDialog(elm.idUrlDialog, false); decodeAudioBuf(xhr.response, url, url); onloadend(); };
            xhr.onerror     = function() { alert('Download error'); onloadend(); };
            xhr.onprogress  = function(e){ elm.idProgressBar.innerText = ((e.loaded / e.total) * 100 | 0) + '%'; };
            //xhr.onloadend = onloadend; // Safari does't make onloadend...? Use onload/onerror only to detect end.
            xhr.send();
        }
        
        ////////////////////////////////////////////////////////////////////////
        // WebSocket server processing
        ////////////////////////////////////////////////////////////////////////
        var MAGIC_DAT = 0x57444154; // 'WDAT'
        var MAGIC_INF = 0x57494E46; // 'WINF'

        function calcBlockSize(mic_opt) {
            mic_opt.block = mic_opt.ch * mic_opt.bit / 8 * mic_opt.sr * BUFFER_MS / 1000 | 0;
            return mic_opt;
        }
        var wsocket = null;
        var FORCE_OPT_CHANGE = 5;
        // Manage WebSocket connection
        function wsConnect() {
            var mic_opt = calcBlockSize({dev: elm.idMicDev.value | 0, ch: elm.idMicCh.value | 0, bit: elm.idMicBit.value | 0, sr: elm.idMicSr.value | 0});
            console.log("WebSocket Opt: " + JSON.stringify(mic_opt));
            view.showDialog(elm.idMicDialog, false);

            if (wsocket && wsocket.URL == elm.idSrcMicUrl.value) {
                // Send restart command by new configuration
                wsocket.opt = mic_opt;
                wsocket.unm = 0;
                wsocket.buf = WaveDecoder.stream(wsocket);
                if (!view.pstate) { // if now playing, force restart
                    view.stop();
                    view.start();
                }
                changeAudioBuf(wsocket.buf, wsocket, wsocket.URL);
            } else {
                // Create new WebSocket connection and set configuration
                try {
                	wsocket = new WebSocket(elm.idSrcMicUrl.value);
               	} catch (e) {
                    console.log('WebSocket create failed');
                    elm.idMicErrMsg.innerText = 'WebSocket create failed (URL="' + elm.idSrcMicUrl.value + '")\n' + e.message;
                    view.showDialog(elm.idMicErrorDialog, true);
               		return;
               	}
                wsocket.binaryType = 'arraybuffer';

                wsocket.onopen = function () {
                    console.log('WebSocket open success ', wsocket.URL);
                    wsocket.opt = mic_opt;
                    wsocket.unm = 0;
                    wsocket.buf = WaveDecoder.stream(wsocket);
                    changeAudioBuf(wsocket.buf, wsocket, wsocket.URL);
                };

                var ws_buf = null;
                wsocket.onmessage = function (e) {
                    // Create concat array
                    var len  = ws_buf ? ws_buf.byteLength : 0;
                    var t    = new Uint8Array(len + e.data.byteLength);
                    if (ws_buf) t.set(ws_buf, 0);
                    t.set(new Uint8Array(e.data), len);
                    ws_buf = t;
                    len += e.data.byteLength;
                    
                    // Parse buffer
                    while (len >= 8) { // sufficient header?
                        var dv = new DataView(ws_buf.buffer);
                        var magic = dv.getUint32(0, 1);
                        var size  = dv.getUint32(4, 1) + 8;
                        if (len < size) break; // insufficient data?
                        
                        // Check data block
                        if (magic === MAGIC_DAT) {
                            // Append received data to on-demand stream buffer
                            var ret = wsocket.buf.append(dv, size);
                            if (ret) { // err
                                if (wsocket.unm++ > FORCE_OPT_CHANGE && !view.pstate) { // another client changes the mic settings...?
                                    view.stop();
                                    wsocket.unm = 0;
                                    wsocket.opt = calcBlockSize(ret);
                                    wsocket.buf.init(wsocket.opt);
                                    changeAudioBuf(wsocket.buf, wsocket, wsocket.URL);
                                    view.start();
                                    console.log('WebSocket force change to', JSON.stringify(wsocket.opt));
                                }
                            } else { // success
                                wsocket.unm = 0;
                            }
                        } else if (magic === MAGIC_INF) { // stop information
                            var code = dv.getUint32(8, 1);
                            var msg  = String.fromCharCode.apply(null, ws_buf.subarray(12, size));
                            console.log('WebSocket get INF', code, msg);
                            if (code) { // error info?
                                elm.idMicErrMsg.innerText = msg + ' (Err:' + code + ')';
                                view.showDialog(elm.idMicErrorDialog, true);
                                view.stop();
                            }
                        } else {
                            console.log('WebSocket get unknwon data block', magic, size, len);
                        }
                        
                        // Truncate current data
                        len -= size;
                        ws_buf = len ? ws_buf.subarray(-len) : null;
                    }
                };

                // Stop player if on error
                wsocket.onclose = function (e) {
                    console.log('WebSocket close ', e? e.code : 'from error');
                    if (wsocket) {
                        wsocket.disable = true;
                        view.stop();
                        wsocket = null;
                    }
                };

                // Stop player if on error
                wsocket.onerror = function (error) {
                    console.log('WebSocket Error ');
                    wsocket.onclose();

                    // onerror can't get detail error code, msg, etc...
                    elm.idMicErrMsg.innerText = 'WebSocket disconnect (' + error.target.url + ')';
                    view.showDialog(elm.idMicErrorDialog, true);
                };
            }
        }

        ////////////////////////////////////////////////////////////////////////
        // Plugin
        ////////////////////////////////////////////////////////////////////////
        function changePlugin(v) {
            var deinit = plugin.deinit;
            if (deinit) {
                plugin = {};
                deinit();
            }
            if (v != 'None') {
                plugin = window[v];
                if (!plugin.init(model, view, elm)) {
                    plugin = {};
                    elm.idPluginNone.checked = true;
                } else if (!view.pstate) {
                    view.update({play: true});
                }
            }
        }

        // Event callbacks
        var DOM_CALLBACKS = [
            //  Input Source ///////////////////////////////////////////////////
            ['idSelinputTitle', 'click',    function()  { view.toggleConfBox(elm.idSelinputItem);   }],
            //['idSrcMic',        'click',    function()  { openMic();                                }],
            ['idSrcMic',        'click',    function()  { view.showDialog(elm.idMicDialog);         }],
            ['idSrcLocal',      'click',    function()  { elm.idSrcLocalFile.click();               }],
            ['idSrcHttp',       'click',    function()  { view.showDialog(elm.idUrlDialog);         }],
            ['idSrcLocalFile',  'change',   function(e) { selFile(e.target.files);                  }],

            //  Playback control ///////////////////////////////////////////////
            ['idPlayTitle',     'click',    function()  { view.toggleConfBox(elm.idPlayItem);       }],
            ['idStart',         'click',    function()  { view.start();                             }],
            ['idStop',          'click',    function()  { view.stop();                              }],
            ['idPause',         'click',    function()  { view.pause();                             }],
            ['idVolume',        'change',   function(e) { view.changeVolume       (e.target.value); }],
            ['idPBSRange',      'change',   function(e) { view.changePlaybackSpeed(e.target.value); }],

            // Flow config /////////////////////////////////////////////////////
            ['idFlowConfTitle', 'click',    function()  { view.toggleConfBox(elm.idFlowItem);       }],
            ['idFlowNone',      'change',   function()  { view.changeFlowMode();                    }],
            ['idFlowRoll',      'change',   function()  { view.changeFlowMode();                    }],
            ['idFlowOver',      'change',   function()  { view.changeFlowMode();                    }],
            ['idFDSRange',      'change',   function(e) { view.changeFDS2    (e.target.value);      }],
            ['idTimeGrid',      'change',   function(e) { view.changeTimeGrid(e.target.checked);    }],

            // Frequency config ////////////////////////////////////////////////
            ['idFreqConfTitle', 'click',    function()  { view.toggleConfBox(elm.idFreqConfItem);   }],
            ['idFreqLinear',    'change',   function()  { view.changeFreqMode(0);                   }],
            ['idFreqLog',       'change',   function()  { view.changeFreqMode(1);                   }],
            ['idFreqMin',       'change',   function()  { view.changeFreqRange(1);                  }],
            ['idFreqMax',       'change',   function()  { view.changeFreqRange(2);                  }],
            ['idFreqGrid',      'change',   function(e) { view.changeFreqGrid(e.target.checked);    }],
            ['idFreqFull',      'change',   function(e) { view.changeFreqFull(e.target.checked);    }],

            // Amplitude config ////////////////////////////////////////////////
            ['idAmplConfTitle', 'click',    function()  { view.toggleConfBox(elm.idAmplItem);       }],
            ['idAmplLinear',    'change',   function()  { view.changeAmplMode (0);                  }],
            ['idAmpldB',        'change',   function()  { view.changeAmplMode (1);                  }],
            ['idAmplMin',       'change',   function()  { view.changeAmplRange(1);                  }],
            ['idAmplMax',       'change',   function()  { view.changeAmplRange(2);                  }],
            ['idAmplGrid',      'change',   function(e) { view.changeAmplGrid(e.target.checked);    }],

            // Amplitude palette ///////////////////////////////////////////////
            ['idColorTitle',    'click',    function()  { view.toggleConfBox(elm.idColorItem);                              }],
            ['idColorSel',      'change',   function()  { view.changeColor(elm.idColorSel.value, elm.idPalInvert.checked);  }],
            ['idPalInvert',     'change',   function()  { view.changeColor(elm.idColorSel.value, elm.idPalInvert.checked);  }],

            // Graph option ////////////////////////////////////////////////////
            ['idGraphConfTitle','click',    function()  { view.toggleConfBox(elm.idGraphConfItem);      }],
            ['idLerp',          'change',   function(e) { view.changeLerp(e.target.checked);            }],
            ['idCurNoOL',       'change',   function(e) { view.changeNoOverlap(e.target.checked);       }],
            ['idWaveMax',       'change',   function(e) { view.changeWaveMax (e.target.checked);        }],
            ['idWaveAvg',       'change',   function(e) { view.changeWaveAvg (e.target.checked);        }],
            ['idWavePeak',      'change',   function(e) { view.changeWavePeak(e.target.checked);        }],
            ['idPeakPeriod',    'change',   function(e) { view.changePeakPeriod(e.target.value);        }],
            ['idClear',         'click',    function()  { model.clearStat();                            }],

            // FFT config //////////////////////////////////////////////////////
            ['idFFTConfTitle',  'click',    function()  { view.toggleConfBox(elm.idFFTItem);            }],
            ['idFFTSel',        'change',   function(e) { model.fft_size        = e.target.value;       }],
            ['idFFTCh',         'change',   function(e) { model.fft_ch          = e.target.value;       }],
            ['idFFTWindow',     'change',   function(e) { model.fft_winfn       = e.target.value;       }],
            ['idOverlap',       'change',   function(e) { model.fft_overlap2    = e.target.value;       }],

            // Plugin config ///////////////////////////////////////////////////
            ['idPluginConfTitle','click',   function()  { view.toggleConfBox(elm.idPluginItem);         }],
            ['idPluginNone',    'change',   function(e) { changePlugin(e.target.value);                 }],
            ['idPluginJJY',     'change',   function(e) { changePlugin(e.target.value);                 }],

            // Debug config ////////////////////////////////////////////////////
            ['idDebugConfTitle','click',    function()  { view.toggleConfBox(elm.idDebugConfItem);      }],
            ['idOLDebug',       'change',   function(e) { view.changeOLDebug (e.target.checked);        }],
            ['idFpsDebug',      'change',   function(e) { view.changeFpsDebug(e.target.checked);        }],

            // Mic dialog //////////////////////////////////////////////////////
            ['idMicStart',      'click',    function(e) { wsConnect(e);                                 }],
            ['idMicCancel',     'click',    function()  { view.showDialog(elm.idMicDialog,    false);   }],
            ['idCloseErr',      'click',    function()  { view.showDialog(elm.idMicErrorDialog, false); }],

            // Download dialog /////////////////////////////////////////////////
            ['idDownloadStart', 'click',    function(e) { downloadFile(e);                              }],
            ['idCloseUrl',      'click',    function()  { view.showDialog(elm.idUrlDialog,    false);   }],
            ['idClosePrg',      'click',    function()  { view.showDialog(elm.idDecodeDialog, false);   }],

            // Drag & Drop /////////////////////////////////////////////////////
            ['idDropDiv',       'dragover', function(e) { e.preventDefault();                           }],
            ['idDropDiv',       'drop',     function(e) { selFile(e.dataTransfer.files, true);          }],

            // Resizeable window/Div ///////////////////////////////////////////
            ['idConfDiv',       'mouseup',  function()  { view.resizeAll();     }],
            ['idWaveDiv',       'mouseup',  function()  { view.resizeAll();     }],
            ['window',          'resize',   function(e) { view.resizeAll(e);    }],
        ];

        // Canvas callbacks
        var TOUCH_CALLBACKS = [
            ['idColorCanvas', 'touchstart', function()  { mouse.colorDown ();   }],
            ['idWaveCanvas',  'touchstart', function()  { mouse.waveDown  ();   }],
            ['idFlowCanvas',  'touchstart', function()  { mouse.flowDown  ();   }],
        ];
        var MOUSE_CALLBACKS = [
            ['idColorCanvas', 'mousedown',  function()  { mouse.colorDown ();   }],
            ['idWaveCanvas',  'mousedown',  function()  { mouse.waveDown  ();   }],
            ['idFlowCanvas',  'mousedown',  function()  { mouse.flowDown  ();   }],
            ['idColorCanvas', 'mousewheel', function()  { mouse.colorWheel();   }],
            ['idWaveCanvas',  'mousewheel', function()  { mouse.waveWheel ();   }],
            ['idFlowCanvas',  'mousewheel', function()  { mouse.flowWheel ();   }],
        ];

        // Come HTML checking...
        function checkHTML5Ext() {
            // Replace to standard object name from vendor prefixed object
            window.URL              = window.URL             || window.webkitURL             || window.mozURL             || window.msURL             || null;
            window.AudioContext     = window.AudioContext    || window.webkitAudioContext    || window.mozAudioContext    || window.msAudioContext    || null;
            navigator.getUserMedia  = navigator.getUserMedia || navigator.webkitGetUserMedia || navigator.mozGetUserMedia || navigator.msGetUserMedia || null;

            // Disable the invalid HTML5 functions
            // Microphone
            /*
            if (!navigator.getUserMedia){
                elm.idSrcMic.title    = 'This browser cannot use the microphone input!';
                elm.idSrcMic.disabled = true;
            }
            */
            
            // File type input (for local file acccess)
            if (elm.idSrcLocalFile.disabled){
                elm.idSrcLocal.title    = 'This browser cannot use the type of input as local file!';
                elm.idSrcLocal.disabled = true;
            }
            
            // Create HTML5 audio context if exist
            if (window.AudioContext) audio_ctx = new window.AudioContext();
            if (!audio_ctx){ // Web Audio API
                //elm.idVolume.disabled = true;
                //elm.idVolume.title = 'This browser cannot use AudioContext!';
                //elm.idVolume.value = 0;       // mute
                
                // Only support WAV file
                elm.idSrcLocalFile.accept       = 'audio/wav';
                elm.idSrcLocal.title            = 'Open an WAV file on your computer';
                elm.idDownloadNote.innerHTML    = 'This browser does not support the Web Audio API (AudioContext).<br>So, please specify the WAV format only.';
                elm.idDownloadNote.style.color  = '#f55';
                
                // if Web Audio API does not support on this browser, use Audio tag
                if(!elm.idAudio.canPlayType) elm.idAudio = null; // Audio also unusable!
                else {
                    //elm.idAudio.onloadeddata = function(e) { ge1 = e, ge2 = event; alert('loaded');};
                    //elm.idAudio.addEventListener('loadeddata', function(e) { ge3 = e, ge4 = event; alert('loaded2');}, false) // OK
                    //elm.idAudio.src = 'sample/piano_and_beat.mp3';
                    //elm.idAudio.play();
                }
            }
        }
        
        ///////////////////////////////////////////////////////////////////////////////
        // Initialize (onload)
        ///////////////////////////////////////////////////////////////////////////////
        function init() {
            // Init view by default value on HTML 
            view.init();

            // Set model parameters by default value described on HTML 
            model.fft_ch        = elm.idFFTCh.value;
            model.fft_size      = elm.idFFTSel.value;
            model.fft_winfn     = elm.idFFTWindow.value;
            model.fft_overlap2  = elm.idOverlap.value;

            // Check the device type (touch or mouse, easy check using UA, now...)
            touch_dev = navigator.userAgent.search(/Android|iPad|iPhone|iPod/) + 1;

            // Some browser have not yet supported some HTML5 feature, so check it.
            checkHTML5Ext();

            // Add all event handlers for each device type
            DOM_CALLBACKS.concat((touch_dev? TOUCH_CALLBACKS : MOUSE_CALLBACKS)).forEach(function(v) {
                elm[v[0]].addEventListener(v[1], v[2], v[3]);
            });
            
            // Add min/max attributes to specified range elements for some browser which does not support input of number type input
            if (!elm.idFreqMin.max){
                console.log('This browser have not yet suppport "number" input type');
                var NUMBER_TYPE_INPUTS = [elm.idFreqMin, elm.idFreqMax, elm.idAmplMin, elm.idAmplMax];
                var ATTR_LIST = ['min', 'max', 'step'];
                for (var i = 0, j; (j = NUMBER_TYPE_INPUTS[i]); ++i){
                    for (var n = 0, m; (m = ATTR_LIST[n]); ++n){
                        j[m] = j.getAttribute(m);
                    }
                }
            }
            
            // Finally, resize by current browser window size and enable the auto-redraw
            view.resizeAll();
            view.redraw(true);
        }
        
        // public method of controller
        return {
            init: init,
        };
    })();

    // for debug
    function debugLog(msg) { view.debugLog(msg); }

    // public method of SpeAnaWeb //////////////////////////////////////////////
    return {
        onload: controller.init,
    };
})();

window.onload = SpeAnaWeb.onload;
