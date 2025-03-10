////////////////////////////////////////////////////////////////////////////////
// utils.js: Util funcs for SpeAna
// Copyright (c) 2012 rinos4u, released under the MIT open source license.
////////////////////////////////////////////////////////////////////////////////

// public methods

// get regulated value of specified range
function getRange(v, min, max) {
    if(v < min) return min;
    if(v > max) return max;
    return v;
}

// Array comparison
function arrayComp(ary1, ary2) {
    if (typeof(ary1) !== 'object' || typeof(ary2) !== 'object') return false; // not array
    var len = ary1.length;
    if (len !== ary2.length) return false;
    for (var i = 0; i < len; ++i) if(ary1[i] !== ary2[i]) return false;
    return true;
}

// dB transform
var MIN_dB      = -120;
var MIN_MAG     = Math.pow(10, MIN_dB / 20);
var LOG10E20    = 20 * Math.LOG10E;

function toDB(v) {
    return LOG10E20 * Math.log(Math.max(MIN_MAG, v));
}