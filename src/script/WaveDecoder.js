////////////////////////////////////////////////////////////////////////////////
// WaveDecoder.js: Wave file decoder for SpeAna
// Copyright (c) 2012 rinos4u, released under the MIT open source license.
////////////////////////////////////////////////////////////////////////////////

// for lint...
/*var window, console;
var DataView, Uint8Array, Float32Array;
//*/

// DataView compatible object for Firefox (which is not support DataView!)
var MyDataView = function(buf) { // buf: ArrayBuffer type
    'use strict';

    var u8ary = new Uint8Array(buf);
    
    // Get unsigned value from multi-byte array
    function getValue(offset, little, size) {
        var ret = 0;
        if (little) {
            while(size--) ret = ret * 0x100 + u8ary[offset + size];
        } else {
            while(size--) ret = ret * 0x100 + u8ary[offset++];
        }
        return ret;
    }

    // Two's complement
    function signVal(val, half) {
        return (val < half) ? val : (val - half * 2);
    }

    // DataView compatible public method (not full APIs, just for WaveDecodeBuffer)
    return {
        // method
        getUint8:   function(offset)         { return         u8ary[offset];                            },
        getInt8:    function(offset)         { return signVal(u8ary[offset],               128);        },
        getUint16:  function(offset, little) { return         getValue(offset, little, 2);              },
        getInt16:   function(offset, little) { return signVal(getValue(offset, little, 2), 32768 );     },
        getUint32:  function(offset, little) { return         getValue(offset, little, 4);              },
        getInt32:   function(offset, little) { return signVal(getValue(offset, little, 4), 2147483648); },
        
        // getter
        get byteLength() { return u8ary.length; },
    };
};


////////////////////////////////////////////////////////////////////////////////
// WaveDecodeBuffer
////////////////////////////////////////////////////////////////////////////////
// Wave parser for substitution of Web Audio API
var WaveDecoder = (function() {
    'use strict';

    // Wave magic
    var RIFF_HEADER     = 0x52494646; // RIFF
    var WAVE_HEADER     = 0x57415645; // WAVE
    var WAVE_CHUNK_FMT  = 0x666D7420; // fmt 
    var WAVE_CHUNK_DAT  = 0x64617461; // data

    // Normalize function
    var NORM_FUNCS = [
        function(dv, p) { return (dv.getUint8(p) - 128)       /     128; }, //  8bit: unsigned(       0..    255)
        function(dv, p) { return  dv.getInt16(p, 1)           /   32768; }, // 16bit: signed  (  -32768..  32767)
        function(dv, p) { return (dv.getInt32(p - 1, 1) >> 8) / 8388608; }, // 24bit: signed  (-8388608..8388607)
    ];

    // Parse wave file and return sound buffer object
    function decode(buf, info) {
        // Check wave header
        var dv = window.DataView ? new DataView(buf) : MyDataView(buf);
        if (dv.getUint32(0) != RIFF_HEADER)                     return {error: 'Invalid RIFF format of ' + info};
        if (dv.getUint32(8) != WAVE_HEADER)                     return {error: 'Invalid WAVE format of ' + info};

        // Init compatible mebers of Web Audio API
        var m_ch  = 0; // number of channels
        var m_sr  = 0; // sampling rate
        var m_bit = 0; // bit depth

        // Check wave chunks
        var format = 0;
        for (var pos = 12; pos + 8 < dv.byteLength; pos += size) {
            var chunk = dv.getUint32(pos);
            var size  = dv.getUint32(pos + 4, 1);
            if ((pos += 8) + size > dv.byteLength)              return {error: 'WAV file is too short'};

            switch (chunk) {
            case WAVE_CHUNK_FMT:
                // Check ID (only 1:PCM)
                format = dv.getUint16(pos, 1);
                if (format != 1)                                return {error: 'Invalid WAV format (1:PCM only): ' + format};

                // Check channel number (1>ch)
                m_ch = dv.getUint16(pos + 2, 1);
                if (m_ch < 1)                                   return {error: 'Invalid channel number (>= 1ch): ' + m_ch};

                // Check sampling rate (1kHz>sr)
                m_sr = dv.getUint32(pos + 4, 1);
                if (m_sr < 1000)                                return {error: 'Invalid sampling rate (>= 1kHz): ' + m_sr};

                // Check bits (8, 16, 24)
                m_bit = dv.getUint16(pos + 14, 1);
                if (m_bit != 8 && m_bit != 16 && m_bit != 24)   return {error: 'Invalid bit depth (8, 16, 24 bit only): ' + m_bit};
                break;

            case WAVE_CHUNK_DAT:
                // FMT chunk must be arranged before DAT chunk
                if (format != 1)                                return {error: 'Invalid WAV format'};

                // Finish format check of wave file, then return sound buffer object
                var b8    =  m_bit / 8;
                var m_len = size / m_ch / b8;
                var m_dat = [];
                for (var i = 0; i < m_ch; ++i) {
                    m_dat[i] = new Float32Array(m_len); // same as AudioBuffer
                }

                // Normalize buffer (same as AudioBuffer)
                var normfn = NORM_FUNCS[b8 - 1];
                for (i = 0; i < m_len; ++i) {
                    for (var j = 0; j < m_ch; ++j, pos += b8) {
                        m_dat[j][i] = normfn(dv, pos);
                    }
                }

                // public method (AudioBuffer compatible APIs)
                return {
                    // method
                    getChannelData: function(n) { return m_dat[n]; },

                    // getter
                    get sampleRate()            { return m_sr; },
                    get numberOfChannels()      { return m_ch; },
                    get duration()              { return m_len / m_sr; },
                    get length()                { return m_len; },
                    get bits()                  { return m_bit; },
                };

            default:
                // Ignore all other chunk
                break;
            }
        }

        return {error: 'No dat section in ' + info};
    }

    // Return on-demand stream buffer object
    function stream(wsocket) {
        var m_start;
        var m_cur;
        var m_end;
        var m_chain;
        var m_free;
        var m_res = [];
        
        var m_sr;
        var m_ch;
        var m_bit;

        // Init/Free all vars
        function init (opt) {
            m_start = 0;
            m_cur   = 0;
            m_end   = 0;
            m_res   = [];
            m_chain = [];
            m_free  = [];
            
            if (opt) {
                m_sr  = opt.sr;
                m_ch  = opt.ch;
                m_bit = opt.bit;
            }
        }
        // Append next buffer to stream chain
        function append(dv, size) {
            var dat_sr  = dv.getUint32( 8, 1);
            var dat_ch  = dv.getUint8 (12, 1);
            var dat_bit = dv.getUint8 (13, 1);
            var dat_rfu = dv.getUint16(14, 1);
            if (dat_sr  != m_sr || dat_ch  != m_ch || dat_bit != m_bit) {
                console.log('WebSocket data unmatch', size, m_sr + ':' + dat_sr + 'Hz', m_ch + ':' + dat_ch + 'ch', m_bit + ':' + dat_bit + 'bit', dat_rfu);
                return {ch: dat_ch, bit: dat_bit, sr: dat_sr}; // unmatch (return new data opt) 
            }

            // Add translated buffer to chain
            var ch_dat   = m_free.pop() || [];
            var b8       = dat_bit / 8;
            var len      = (size - 16) / b8 / m_ch;
            var normfn   = NORM_FUNCS[b8 - 1];
            ch_dat.start = m_cur;
            m_cur       += len;
            ch_dat.end   = m_cur;

            //console.log('StreamBuffer Append:', m_chain.length, !ch_dat[0], m_free.length, m_start, m_end);

            // Create each channel arrays
            if (!ch_dat[0]) { // not from free list?
                var nch = (m_ch > 1)? m_ch + 1 : 1;
                for (var i = 0; i < nch; ++i) ch_dat[i] = new Float32Array(len);
                if (m_ch === 1) ch_dat[1] = ch_dat[0]; // share merge for 1ch data
            }
            
            // Calc normalized buffer
            var invn = 1 / ch;
            var idx  = 16 - b8;
            while (len--) {
                var sum = 0;
                for (var ch = 1; ch <= m_ch; ++ch) {
                    var val = normfn(dv, idx += b8);
                    ch_dat[ch][len] = val;
                    sum += val;
                }
                if (m_ch > 1) ch_dat[0][len] = sum * invn; // merge
            }
            m_chain.push(ch_dat);
            m_end = m_cur;
        }
        
        // Free the useless buffer chains
        function waste(end) {
            if (end === null) {
                // init buffer
                init();
                console.log('StreamBuffer waste all');
            } else {
                // move useless buffers to free list
                for (var i = 0; m_chain[i].end < end; ++i);
                if (i) {
                    [].push.apply(m_free, m_chain.splice(0, i));
                    m_start = m_chain[0].start;
                    //console.log('StreamBuffer waste:', i, end, m_start, m_end);
                }
            }
        }
        
        // Check the buffer range
        function inRange(offset) {
            //console.log('StreamBuffer inRange', m_start, m_end, offset);
            return m_start <= offset && offset < m_end;
        }
        
        // Get specified range buffer, like getChannelData
        function getBuf(start, end, ch){
            if (start < m_start || m_end <= end) {
                console.log('StreamBuffer: Data not ready: start', start, m_start, 'end:', m_end, end);
                return false;
            }
            var len = end - start;
            if (m_res.length < len) {
                m_res = new Float32Array(len); // realloc
            }

            // Search first target block
            var cpos = 0;
            while (start >= m_chain[cpos].end) ++cpos;

            // Set selected cahnnel data to result buffer
            for (var idx = 0; idx < len; ++cpos) {
                var block = m_chain[cpos];
                var pos   = start - block.start;
                var size  = Math.min(block.end - start, len - idx);
                m_res.set(block[ch].subarray(pos, pos + size), idx);
                idx   += size;
                start += size;
            }
            return m_res.subarray(0, len);
        }
        
        // Init internal buffer
        init(wsocket.opt);

        // public method (AudioBuffer compatible APIs)
        return {
            // Special method for stream buffer
            append:     append,
            waste:      waste,
            inRange:    inRange,
            getBuf:     getBuf,
            init:       init,

            // getter
            get sampleRate()            { return m_sr; },
            get numberOfChannels()      { return m_ch; },
            get duration()              { return 0; },
            get length()                { return 0; },
            get bits()                  { return m_bit; },
        };
    }

    // public method
    return {
        decode: decode, // Decode wave file
        stream: stream, // Create on-demand stream buffer
    };
})();
