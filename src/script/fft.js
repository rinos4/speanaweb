////////////////////////////////////////////////////////////////////////////////
// fft.js: FFT lib for SpeAna (from fft.lua)
// Copyright (c) 2012 rinos4u, released under the MIT open source license.
////////////////////////////////////////////////////////////////////////////////

// for lint...
/*
var Uint32Array, Float32Array;
//*/


// FFT object generator for fixed block size
var FFT = (function () {
    'use strict';

    // Constant values for FFT
    var PI2      = Math.PI * 2;
    var PI4      = PI2 * 2;

    var LOG10E20 = Math.LOG10E * 20;
    var RECT_WIN = function () { return 1; }; // Default window function is rectangle

    // Create a new FFT object by specified block size (block_size must be 2^n, n > 3)
    function create(block_size, winfn) {
        // Create size related recycle arrays.
        // Use ffi-double/int array internally. It's faster than standard Lua table (25%)
        // Use concated tcosi[],treim[] array instead of divided cos[],sin[],real[],imag[]
        // arrays for vector processing. Concat array is faster than divided array (30%)
        // TODO: write rfft algorithm for more optimization...?
        var block_dbl  = block_size << 1;
        var block_half = block_size >> 1;
        var inv_half   = 1 / block_half;
        var twinf = new Float32Array(block_size);
        var trvs2 = new Uint32Array (block_size);
        var tcosi = new Float32Array(block_dbl);
        var treim = new Float32Array(block_dbl);
        var tres  = new Float32Array(block_half);

        // Cache reverse*2/sin,cos (constant table)
        (function init() {
            for (var i = 2; i < block_dbl; i += 2) {
                var rad = -PI2 / i;
                tcosi[i    ] = Math.cos(rad);
                tcosi[i + 1] = Math.sin(rad);
            }

            trvs2[0] = 0;
            for(var up = 1, dn = block_size; up < block_size; up <<= 1, dn >>= 1) {
                for (i = 0; i < up; ++i) {
                    trvs2[up + i] = trvs2[i] + dn;
                }
            }
        })();

        // Cache window function table
        function initWF(winfn) {
            // Use Rectangle window if winfn is not specified
            winfn = winfn || RECT_WIN;
            var iw = 1 / (block_size - 1);
            for (var i = 0; i < block_size; ++i) {
                twinf[i] = winfn(i * iw);
            }
        }
        initWF(winfn);

        // Perform a forward transform (Critical function for performance)
        // All arithmetic (including sqrt) in fft() can be executed by the VFPv2 instruction.
        // If more performance will be needed, change this by vector-asm and call it from ffi.
        // (Block size >= 16. So, we can optimize to use all 16 double-precision units of VFP.)
        // DP MUL, MAC   2 cycles
        // DP DIV, SQRT 28 cycles
        // All others    1 cycle
        function fft(buf, offset) {
            // Init complex
            for (var i = 0; i < block_size; ++i) {
                var ri = trvs2[i];
                treim[ri    ] = buf[offset + i] * twinf[i];
                treim[ri + 1] = 0;
            }

            // Butterfly
            for (var up = 2, up2; up < block_dbl; up = up2) {
                var p_re = tcosi[up    ];
                var p_im = tcosi[up + 1];
                var c_re = 1;
                var c_im = 0;

                up2 = up << 1;
                for (i = 0; i < up; i += 2) {
                    for (var j = i; j < block_dbl; j += up2) {
                        var k = j + up;
                        var j_re = treim[j    ];
                        var j_im = treim[j + 1];
                        var k_re = treim[k    ];
                        var k_im = treim[k + 1];
                        var t_re = c_re * k_re - c_im * k_im;
                        var t_im = c_re * k_im + c_im * k_re;
                        treim[k    ] = j_re - t_re;
                        treim[k + 1] = j_im - t_im;
                        treim[j    ] = j_re + t_re;
                        treim[j + 1] = j_im + t_im;
                    }
                    var t= c_re * p_re - c_im * p_im;
                    c_im = c_re * p_im + c_im * p_re;
                    c_re = t;
                }
            }

            // Transform from complex
            var sqrt = Math.sqrt;
            for (i = 0; i < block_half; ++i) {
                var i2 = i << 1;
                var re = treim[i2    ];
                var im = treim[i2 + 1];
                tres[i] = sqrt(re * re + im * im) * inv_half;
            }
        }

        // FFT with decibel transform
        function trans(buf, offset, mindB) {
            fft(buf, offset);
            if (mindB) {
                var log = Math.log;
                var max = Math.max;
                var mrl = Math.pow(10, mindB * 0.05); // mindB/20
                for (var i = 0; i < block_half; ++i) {
                    tres[i] = LOG10E20 * log(max(mrl, tres[i]));
                }
            }
        }
        
        // public method
        return {
            trans:          trans,
            changeWindow:  initWF,

            // getter
            get block_size(){ return block_size; },
            get half_size() { return block_half; },
            get result()    { return tres; }, // contents of array can be modified...
        };
    }

    // public method
    return {
        create:     create,

        // Pre-defined window functions for create fn
        rect:       RECT_WIN,
        hann:       function(x) { return 0.5  - 0.5  * Math.cos(PI2 * x); },
        hamming:    function(x) { return 0.54 - 0.46 * Math.cos(PI2 * x); },
        blackman:   function(x) { return 0.42 - 0.5  * Math.cos(PI2 * x) + 0.08 * Math.cos(PI4 * x); },
        bartlett:   function(x) { return 1 - Math.abs(2 * x - 1); },
        sine:       function(x) { return Math.sin(Math.PI * x); },
    };
})();
