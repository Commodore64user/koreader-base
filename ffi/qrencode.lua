--- The qrcode library is licensed under the 3-clause BSD license (aka "new BSD")
--- To get in contact with the author, mail to <gundlach@speedata.de>.
---
--- Please report bugs on the [github project page](http://speedata.github.io/luaqrcode/).
-- Copyright (c) 2012-2020, Patrick Gundlach and contributors, see https://github.com/speedata/luaqrcode
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--	 * Redistributions of source code must retain the above copyright
--	   notice, this list of conditions and the following disclaimer.
--	 * Redistributions in binary form must reproduce the above copyright
--	   notice, this list of conditions and the following disclaimer in the
--	   documentation and/or other materials provided with the distribution.
--	 * Neither the name of SPEEDATA nor the
--	   names of its contributors may be used to endorse or promote products
--	   derived from this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
-- ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
-- WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL SPEEDATA GMBH BE LIABLE FOR ANY
-- DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
-- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
-- LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
-- ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
-- SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

local max, min = math.max, math.min
local floor, abs = math.floor, math.abs
local byte, sub, rep = string.byte, string.sub, string.rep
local match, format = string.match, string.format

local bit = require("bit")
local band, bor, bxor, lshift, rshift = bit.band, bit.bor, bit.bxor, bit.lshift, bit.rshift

--- Helper functions
--- ================

local function set_cell(matrix, size, x, y, val)
	matrix[(y - 1) * size + x] = val
end

-- BitWriter for memory-efficient data buffering
local BitWriter = {}
BitWriter.__index = BitWriter
function BitWriter.new()
	return setmetatable({ buf = {}, len = 0, acc = 0, bits = 0 }, BitWriter)
end

function BitWriter:write(val, len)
	self.acc = bor(lshift(self.acc, len), val)
	self.bits = self.bits + len
	while self.bits >= 8 do
		self.bits = self.bits - 8
		self.len = self.len + 1
		self.buf[self.len] = band(rshift(self.acc, self.bits), 0xFF)
	end
end

function BitWriter:flush()
	if self.bits > 0 then
		self.len = self.len + 1
		self.buf[self.len] = band(lshift(self.acc, 8 - self.bits), 0xFF)
		self.bits = 0
	end
	return self.buf
end


--- Step 1: Determine version, ec level and mode for codeword
--- =========================================================

local function get_mode(str)
	if match(str,"^[0-9]+$") then return 1
	elseif match(str,"^[0-9A-Z $%%*./:+-]+$") then return 2
	else return 4 end
end

local capacity = {
	{  19,   16,   13,    9},{  34,   28,   22,   16},{  55,   44,   34,   26},{  80,   64,   48,   36},
	{ 108,   86,   62,   46},{ 136,  108,   76,   60},{ 156,  124,   88,   66},{ 194,  154,  110,   86},
	{ 232,  182,  132,  100},{ 274,  216,  154,  122},{ 324,  254,  180,  140},{ 370,  290,  206,  158},
	{ 428,  334,  244,  180},{ 461,  365,  261,  197},{ 523,  415,  295,  223},{ 589,  453,  325,  253},
	{ 647,  507,  367,  283},{ 721,  563,  397,  313},{ 795,  627,  445,  341},{ 861,  669,  485,  385},
	{ 932,  714,  512,  406},{1006,  782,  568,  442},{1094,  860,  614,  464},{1174,  914,  664,  514},
	{1276, 1000,  718,  538},{1370, 1062,  754,  596},{1468, 1128,  808,  628},{1531, 1193,  871,  661},
	{1631, 1267,  911,  701},{1735, 1373,  985,  745},{1843, 1455, 1033,  793},{1955, 1541, 1115,  845},
	{2071, 1631, 1171,  901},{2191, 1725, 1231,  961},{2306, 1812, 1286,  986},{2434, 1914, 1354, 1054},
	{2566, 1992, 1426, 1096},{2702, 2102, 1502, 1142},{2812, 2216, 1582, 1222},{2956, 2334, 1666, 1276},
}

local function get_version_eclevel(len,mode,requested_ec_level)
	local local_mode = mode
	if mode == 4 then local_mode = 3 elseif mode == 8 then local_mode = 4 end
	assert(local_mode <= 4)

	local bits, digits, modebits, c
	local tab = { {10,9,8,8},{12,11,16,10},{14,13,16,12} }
	local minversion = 99
	local maxec_level = requested_ec_level or 1
	local minlv, maxlv = 1, 4
	if requested_ec_level and requested_ec_level >= 1 and requested_ec_level <= 4 then
		minlv = requested_ec_level
		maxlv = requested_ec_level
	end
	for ec_level = minlv, maxlv do
		for version = 1, #capacity do
			bits = capacity[version][ec_level] * 8 - 4
			if version < 10 then digits = tab[1][local_mode]
			elseif version < 27 then digits = tab[2][local_mode]
			elseif version <= 40 then digits = tab[3][local_mode] end
			modebits = bits - digits
			if local_mode == 1 then c = floor(modebits * 3 / 10)
			elseif local_mode == 2 then c = floor(modebits * 2 / 11)
			elseif local_mode == 3 then c = floor(modebits * 1 / 8)
			else c = floor(modebits * 1 / 13) end

			if c >= len then
				if version <= minversion then
					minversion = version
					maxec_level = ec_level
				end
				break
			end
		end
	end
	assert(minversion<=40, "Data too long to encode in QR code")
	return minversion, maxec_level
end

local function write_length(bw, str_len, version, mode)
	local i = mode
	if mode == 4 then i = 3 elseif mode == 8 then i = 4 end
	local tab = { {10,9,8,8},{12,11,16,10},{14,13,16,12} }
	local digits
	if version < 10 then digits = tab[1][i]
	elseif version < 27 then digits = tab[2][i]
	elseif version <= 40 then digits = tab[3][i] end
	bw:write(str_len, digits)
end


--- Step 2: Encode data
--- ===================

local asciitbl = {
	    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	36, -1, -1, -1, 37, 38, -1, -1, -1, -1, 39, 40, -1, 41, 42, 43,
	 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 44, -1, -1, -1, -1, -1,
	-1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
	25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, -1, -1, -1, -1, -1,
}

local function encode_data(str, mode, bw)
	if mode == 1 then
		for i = 1, #str, 3 do
			local a = sub(str, i, i+2)
			bw:write(tonumber(a), #a * 3 + 1)
		end
	elseif mode == 2 then
		for i = 1, #str, 2 do
			local a = sub(str, i, i+1)
			if #a == 2 then
				local int = asciitbl[byte(sub(a, 1, 1))] * 45 + asciitbl[byte(sub(a, 2, 2))]
				bw:write(int, 11)
			else
				bw:write(asciitbl[byte(a)], 6)
			end
		end
	elseif mode == 4 then
		for i = 1, #str do
			bw:write(byte(str, i), 8)
		end
	end
end

local function add_pad_data(version, ec_level, bw)
	local cpty = capacity[version][ec_level] * 8
	local current_bits = bw.len * 8 + bw.bits
	local count_to_pad = min(4, cpty - current_bits)
	if count_to_pad > 0 then
		bw:write(0, count_to_pad)
	end
	bw:flush()
	local remaining_bytes = floor(cpty / 8) - bw.len
	for i = 1, remaining_bytes do
		bw.len = bw.len + 1
		bw.buf[bw.len] = i % 2 == 1 and 236 or 17
	end
	return bw.buf
end


--- Step 3: Organize data and calculate error correction code
--- =========================================================

local alpha_int = {
	[0] = 1,
	  2,   4,   8,  16,  32,  64, 128,  29,  58, 116, 232, 205, 135,  19,  38,  76,
	152,  45,  90, 180, 117, 234, 201, 143,   3,   6,  12,  24,  48,  96, 192, 157,
	 39,  78, 156,  37,  74, 148,  53, 106, 212, 181, 119, 238, 193, 159,  35,  70,
	140,   5,  10,  20,  40,  80, 160,  93, 186, 105, 210, 185, 111, 222, 161,  95,
	190,  97, 194, 153,  47,  94, 188, 101, 202, 137,  15,  30,  60, 120, 240, 253,
	231, 211, 187, 107, 214, 177, 127, 254, 225, 223, 163,  91, 182, 113, 226, 217,
	175,  67, 134,  17,  34,  68, 136,  13,  26,  52, 104, 208, 189, 103, 206, 129,
	 31,  62, 124, 248, 237, 199, 147,  59, 118, 236, 197, 151,  51, 102, 204, 133,
	 23,  46,  92, 184, 109, 218, 169,  79, 158,  33,  66, 132,  21,  42,  84, 168,
	 77, 154,  41,  82, 164,  85, 170,  73, 146,  57, 114, 228, 213, 183, 115, 230,
	209, 191,  99, 198, 145,  63, 126, 252, 229, 215, 179, 123, 246, 241, 255, 227,
	219, 171,  75, 150,  49,  98, 196, 149,  55, 110, 220, 165,  87, 174,  65, 130,
	 25,  50, 100, 200, 141,   7,  14,  28,  56, 112, 224, 221, 167,  83, 166,  81,
	162,  89, 178, 121, 242, 249, 239, 195, 155,  43,  86, 172,  69, 138,   9,  18,
	 36,  72, 144,  61, 122, 244, 245, 247, 243, 251, 235, 203, 139,  11,  22,  44,
	 88, 176, 125, 250, 233, 207, 131,  27,  54, 108, 216, 173,  71, 142,   0,   0
}

local int_alpha = {
	[0] = 256,
	0,   1,  25,   2,  50,  26, 198,   3, 223,  51, 238,  27, 104, 199,  75,   4,
	100, 224,  14,  52, 141, 239, 129,  28, 193, 105, 248, 200,   8,  76, 113,   5,
	138, 101,  47, 225,  36,  15,  33,  53, 147, 142, 218, 240,  18, 130,  69,  29,
	181, 194, 125, 106,  39, 249, 185, 201, 154,   9, 120,  77, 228, 114, 166,   6,
	191, 139,  98, 102, 221,  48, 253, 226, 152,  37, 179,  16, 145,  34, 136,  54,
	208, 148, 206, 143, 150, 219, 189, 241, 210,  19,  92, 131,  56,  70,  64,  30,
	 66, 182, 163, 195,  72, 126, 110, 107,  58,  40,  84, 250, 133, 186,  61, 202,
	 94, 155, 159,  10,  21, 121,  43,  78, 212, 229, 172, 115, 243, 167,  87,   7,
	112, 192, 247, 140, 128,  99,  13, 103,  74, 222, 237,  49, 197, 254,  24, 227,
	165, 153, 119,  38, 184, 180, 124,  17,  68, 146, 217,  35,  32, 137,  46,  55,
	 63, 209,  91, 149, 188, 207, 205, 144, 135, 151, 178, 220, 252, 190,  97, 242,
	 86, 211, 171,  20,  42,  93, 158, 132,  60,  57,  83,  71, 109,  65, 162,  31,
	 45,  67, 216, 183, 123, 164, 118, 196,  23,  73, 236, 127,  12, 111, 246, 108,
	161,  59,  82,  41, 157,  85, 170, 251,  96, 134, 177, 187, 204,  62,  90, 203,
	 89,  95, 176, 156, 169, 160,  81,  11, 245,  22, 235, 122, 117,  44, 215,  79,
	174, 213, 233, 230, 231, 173, 232, 116, 214, 244, 234, 168,  80,  88, 175
}

local generator_polynomial = {
	 [7] = { 21, 102, 238, 149, 146, 229,  87,   0},
	[10] = { 45,  32,  94,  64,  70, 118,  61,  46,  67, 251,   0 },
	[13] = { 78, 140, 206, 218, 130, 104, 106, 100,  86, 100, 176, 152,  74,   0 },
	[15] = {105,  99,   5, 124, 140, 237,  58,  58,  51,  37, 202,  91,  61, 183,   8,   0},
	[16] = {120, 225, 194, 182, 169, 147, 191,  91,   3,  76, 161, 102, 109, 107, 104, 120,   0},
	[17] = {136, 163, 243,  39, 150,  99,  24, 147, 214, 206, 123, 239,  43,  78, 206, 139,  43,   0},
	[18] = {153,  96,  98,   5, 179, 252, 148, 152, 187,  79, 170, 118,  97, 184,  94, 158, 234, 215,   0},
	[20] = {190, 188, 212, 212, 164, 156, 239,  83, 225, 221, 180, 202, 187,  26, 163,  61,  50,  79,  60,  17,   0},
	[22] = {231, 165, 105, 160, 134, 219,  80,  98, 172,   8,  74, 200,  53, 221, 109,  14, 230,  93, 242, 247, 171, 210,   0},
	[24] = { 21, 227,  96,  87, 232, 117,   0, 111, 218, 228, 226, 192, 152, 169, 180, 159, 126, 251, 117, 211,  48, 135, 121, 229,   0},
	[26] = { 70, 218, 145, 153, 227,  48, 102,  13, 142, 245,  21, 161,  53, 165,  28, 111, 201, 145,  17, 118, 182, 103,   2, 158, 125, 173,   0},
	[28] = {123,   9,  37, 242, 119, 212, 195,  42,  87, 245,  43,  21, 201, 232,  27, 205, 147, 195, 190, 110, 180, 108, 234, 224, 104, 200, 223, 168,   0},
	[30] = {180, 192,  40, 238, 216, 251,  37, 156, 130, 224, 193, 226, 173,  42, 125, 222,  96, 239,  86, 110,  48,  50, 182, 179,  31, 216, 152, 145, 173, 41, 0}}

local function get_generator_polynomial_adjusted(num_ec_codewords, highest_exponent)
	local gp_alpha = {[0]=0}
	for i = 0, highest_exponent - num_ec_codewords - 1 do
		gp_alpha[i] = 0
	end
	local gp = generator_polynomial[num_ec_codewords]
	for i = 1, num_ec_codewords + 1 do
		gp_alpha[highest_exponent - num_ec_codewords + i - 1] = gp[i]
	end
	return gp_alpha
end

local function calculate_error_correction(mp, num_ec_codewords)
	local len_message = #mp
	local highest_exponent = len_message + num_ec_codewords - 1
	local mp_int = {}
	for i = 1, len_message do
		mp_int[highest_exponent - i + 1] = mp[i]
	end
	for i = 1, highest_exponent - len_message do
		mp_int[i] = 0
	end
	mp_int[0] = 0

	local gp = generator_polynomial[num_ec_codewords]

	while highest_exponent >= num_ec_codewords do
		local exp = int_alpha[mp_int[highest_exponent]]
		if exp ~= 256 then
			for j = highest_exponent, highest_exponent - num_ec_codewords, -1 do
				local gp_val = gp[j - highest_exponent + num_ec_codewords + 1]
				local combined = (gp_val + exp) % 255
				mp_int[j] = bxor(alpha_int[combined], mp_int[j])
			end
		end
		for i = highest_exponent, num_ec_codewords, -1 do
			if mp_int[i] == 0 then highest_exponent = i - 1
			else break end
		end
		if highest_exponent < num_ec_codewords then break end
	end
	local ret = {}
	for i = highest_exponent, 0, -1 do
		ret[#ret + 1] = mp_int[i]
	end
	return ret
end

local ecblocks = {
	{{  1,{ 26, 19, 2}                 },   {  1,{26,16, 4}},                  {  1,{26,13, 6}},                  {  1, {26, 9, 8}               }},
	{{  1,{ 44, 34, 4}                 },   {  1,{44,28, 8}},                  {  1,{44,22,11}},                  {  1, {44,16,14}               }},
	{{  1,{ 70, 55, 7}                 },   {  1,{70,44,13}},                  {  2,{35,17, 9}},                  {  2, {35,13,11}               }},
	{{  1,{100, 80,10}                 },   {  2,{50,32, 9}},                  {  2,{50,24,13}},                  {  4, {25, 9, 8}               }},
	{{  1,{134,108,13}                 },   {  2,{67,43,12}},                  {  2,{33,15, 9},  2,{34,16, 9}},   {  2, {33,11,11},  2,{34,12,11}}},
	{{  2,{ 86, 68, 9}                 },   {  4,{43,27, 8}},                  {  4,{43,19,12}},                  {  4, {43,15,14}               }},
	{{  2,{ 98, 78,10}                 },   {  4,{49,31, 9}},                  {  2,{32,14, 9},  4,{33,15, 9}},   {  4, {39,13,13},  1,{40,14,13}}},
	{{  2,{121, 97,12}                 },   {  2,{60,38,11},  2,{61,39,11}},   {  4,{40,18,11},  2,{41,19,11}},   {  4, {40,14,13},  2,{41,15,13}}},
	{{  2,{146,116,15}                 },   {  3,{58,36,11},  2,{59,37,11}},   {  4,{36,16,10},  4,{37,17,10}},   {  4, {36,12,12},  4,{37,13,12}}},
	{{  2,{ 86, 68, 9},  2,{ 87, 69, 9}},   {  4,{69,43,13},  1,{70,44,13}},   {  6,{43,19,12},  2,{44,20,12}},   {  6, {43,15,14},  2,{44,16,14}}},
	{{  4,{101, 81,10}                 },   {  1,{80,50,15},  4,{81,51,15}},   {  4,{50,22,14},  4,{51,23,14}},   {  3, {36,12,12},  8,{37,13,12}}},
	{{  2,{116, 92,12},  2,{117, 93,12}},   {  6,{58,36,11},  2,{59,37,11}},   {  4,{46,20,13},  6,{47,21,13}},   {  7, {42,14,14},  4,{43,15,14}}},
	{{  4,{133,107,13}                 },   {  8,{59,37,11},  1,{60,38,11}},   {  8,{44,20,12},  4,{45,21,12}},   { 12, {33,11,11},  4,{34,12,11}}},
	{{  3,{145,115,15},  1,{146,116,15}},   {  4,{64,40,12},  5,{65,41,12}},   { 11,{36,16,10},  5,{37,17,10}},   { 11, {36,12,12},  5,{37,13,12}}},
	{{  5,{109, 87,11},  1,{110, 88,11}},   {  5,{65,41,12},  5,{66,42,12}},   {  5,{54,24,15},  7,{55,25,15}},   { 11, {36,12,12},  7,{37,13,12}}},
	{{  5,{122, 98,12},  1,{123, 99,12}},   {  7,{73,45,14},  3,{74,46,14}},   { 15,{43,19,12},  2,{44,20,12}},   {  3, {45,15,15}, 13,{46,16,15}}},
	{{  1,{135,107,14},  5,{136,108,14}},   { 10,{74,46,14},  1,{75,47,14}},   {  1,{50,22,14}, 15,{51,23,14}},   {  2, {42,14,14}, 17,{43,15,14}}},
	{{  5,{150,120,15},  1,{151,121,15}},   {  9,{69,43,13},  4,{70,44,13}},   { 17,{50,22,14},  1,{51,23,14}},   {  2, {42,14,14}, 19,{43,15,14}}},
	{{  3,{141,113,14},  4,{142,114,14}},   {  3,{70,44,13}, 11,{71,45,13}},   { 17,{47,21,13},  4,{48,22,13}},   {  9, {39,13,13}, 16,{40,14,13}}},
	{{  3,{135,107,14},  5,{136,108,14}},   {  3,{67,41,13}, 13,{68,42,13}},   { 15,{54,24,15},  5,{55,25,15}},   { 15, {43,15,14}, 10,{44,16,14}}},
	{{  4,{144,116,14},  4,{145,117,14}},   { 17,{68,42,13}},                  { 17,{50,22,14},  6,{51,23,14}},   { 19, {46,16,15},  6,{47,17,15}}},
	{{  2,{139,111,14},  7,{140,112,14}},   { 17,{74,46,14}},                  {  7,{54,24,15}, 16,{55,25,15}},   { 34, {37,13,12}               }},
	{{  4,{151,121,15},  5,{152,122,15}},   {  4,{75,47,14}, 14,{76,48,14}},   { 11,{54,24,15}, 14,{55,25,15}},   { 16, {45,15,15}, 14,{46,16,15}}},
	{{  6,{147,117,15},  4,{148,118,15}},   {  6,{73,45,14}, 14,{74,46,14}},   { 11,{54,24,15}, 16,{55,25,15}},   { 30, {46,16,15},  2,{47,17,15}}},
	{{  8,{132,106,13},  4,{133,107,13}},   {  8,{75,47,14}, 13,{76,48,14}},   {  7,{54,24,15}, 22,{55,25,15}},   { 22, {45,15,15}, 13,{46,16,15}}},
	{{ 10,{142,114,14},  2,{143,115,14}},   { 19,{74,46,14},  4,{75,47,14}},   { 28,{50,22,14},  6,{51,23,14}},   { 33, {46,16,15},  4,{47,17,15}}},
	{{  8,{152,122,15},  4,{153,123,15}},   { 22,{73,45,14},  3,{74,46,14}},   {  8,{53,23,15}, 26,{54,24,15}},   { 12, {45,15,15}, 28,{46,16,15}}},
	{{  3,{147,117,15}, 10,{148,118,15}},   {  3,{73,45,14}, 23,{74,46,14}},   {  4,{54,24,15}, 31,{55,25,15}},   { 11, {45,15,15}, 31,{46,16,15}}},
	{{  7,{146,116,15},  7,{147,117,15}},   { 21,{73,45,14},  7,{74,46,14}},   {  1,{53,23,15}, 37,{54,24,15}},   { 19, {45,15,15}, 26,{46,16,15}}},
	{{  5,{145,115,15}, 10,{146,116,15}},   { 19,{75,47,14}, 10,{76,48,14}},   { 15,{54,24,15}, 25,{55,25,15}},   { 23, {45,15,15}, 25,{46,16,15}}},
	{{ 13,{145,115,15},  3,{146,116,15}},   {  2,{74,46,14}, 29,{75,47,14}},   { 42,{54,24,15},  1,{55,25,15}},   { 23, {45,15,15}, 28,{46,16,15}}},
	{{ 17,{145,115,15}            	 },   { 10,{74,46,14}, 23,{75,47,14}},   { 10,{54,24,15}, 35,{55,25,15}},   { 19, {45,15,15}, 35,{46,16,15}}},
	{{ 17,{145,115,15},  1,{146,116,15}},   { 14,{74,46,14}, 21,{75,47,14}},   { 29,{54,24,15}, 19,{55,25,15}},   { 11, {45,15,15}, 46,{46,16,15}}},
	{{ 13,{145,115,15},  6,{146,116,15}},   { 14,{74,46,14}, 23,{75,47,14}},   { 44,{54,24,15},  7,{55,25,15}},   { 59, {46,16,15},  1,{47,17,15}}},
	{{ 12,{151,121,15},  7,{152,122,15}},   { 12,{75,47,14}, 26,{76,48,14}},   { 39,{54,24,15}, 14,{55,25,15}},   { 22, {45,15,15}, 41,{46,16,15}}},
	{{  6,{151,121,15}, 14,{152,122,15}},   {  6,{75,47,14}, 34,{76,48,14}},   { 46,{54,24,15}, 10,{55,25,15}},   {  2, {45,15,15}, 64,{46,16,15}}},
	{{ 17,{152,122,15},  4,{153,123,15}},   { 29,{74,46,14}, 14,{75,47,14}},   { 49,{54,24,15}, 10,{55,25,15}},   { 24, {45,15,15}, 46,{46,16,15}}},
	{{  4,{152,122,15}, 18,{153,123,15}},   { 13,{74,46,14}, 32,{75,47,14}},   { 48,{54,24,15}, 14,{55,25,15}},   { 42, {45,15,15}, 32,{46,16,15}}},
	{{ 20,{147,117,15},  4,{148,118,15}},   { 40,{75,47,14},  7,{76,48,14}},   { 43,{54,24,15}, 22,{55,25,15}},   { 10, {45,15,15}, 67,{46,16,15}}},
	{{ 19,{148,118,15},  6,{149,119,15}},   { 18,{75,47,14}, 31,{76,48,14}},   { 34,{54,24,15}, 34,{55,25,15}},   { 20, {45,15,15}, 61,{46,16,15}}}
}

local function arrange_codewords_and_calculate_ec(version, ec_level, data)
	local blocks = ecblocks[version][ec_level]
	local size_datablock_bytes, size_ecblock_bytes
	local datablocks = {}
	local final_ecblocks = {}
	local pos = 1
	for i = 1, #blocks / 2 do
		size_datablock_bytes = blocks[2*i][2]
		size_ecblock_bytes   = blocks[2*i][1] - size_datablock_bytes
		for _ = 1, blocks[2*i - 1] do
			local current_block = {}
			for j = 1, size_datablock_bytes do
				current_block[j] = data[pos]
				pos = pos + 1
			end
			datablocks[#datablocks + 1] = current_block
			final_ecblocks[#final_ecblocks + 1] = calculate_error_correction(current_block, size_ecblock_bytes)
		end
	end

	local arranged_data = {}
	local maxBlockLen = 0
	for i = 1, #datablocks do maxBlockLen = max(maxBlockLen, #datablocks[i]) end
	for p = 1, maxBlockLen do
		for i = 1, #datablocks do
			if p <= #datablocks[i] then arranged_data[#arranged_data + 1] = datablocks[i][p] end
		end
	end
	maxBlockLen = 0
	for i = 1, #final_ecblocks do maxBlockLen = max(maxBlockLen, #final_ecblocks[i]) end
	for p = 1, maxBlockLen do
		for i = 1, #final_ecblocks do
			if p <= #final_ecblocks[i] then arranged_data[#arranged_data + 1] = final_ecblocks[i][p] end
		end
	end
	return arranged_data
end


--- Step 4: Generate matrices via scratchpad and calculate penalty
--- ===============================================================

local alignment_pattern = {
	{},{6,18},{6,22},{6,26},{6,30},{6,34},
	{6,22,38},{6,24,42},{6,26,46},{6,28,50},{6,30,54},{6,32,58},{6,34,62},
	{6,26,46,66},{6,26,48,70},{6,26,50,74},{6,30,54,78},{6,30,56,82},{6,30,58,86},{6,34,62,90},
	{6,28,50,72,94},{6,26,50,74,98},{6,30,54,78,102},{6,28,54,80,106},{6,32,58,84,110},{6,30,58,86,114},{6,34,62,90,118},
	{6,26,50,74,98 ,122},{6,30,54,78,102,126},{6,26,52,78,104,130},{6,30,56,82,108,134},{6,34,60,86,112,138},{6,30,58,86,114,142},{6,34,62,90,118,146},
	{6,30,54,78,102,126,150}, {6,24,50,76,102,128,154},{6,28,54,80,106,132,158},{6,32,58,84,110,136,162},{6,26,54,82,110,138,166},{6,30,58,86,114,142,170}
}

local typeinfo = {
	{ [0] = "111011111000100", "111001011110011", "111110110101010", "111100010011101", "110011000101111", "110001100011000", "110110001000001", "110100101110110" },
	{ [0] = "101010000010010", "101000100100101", "101111001111100", "101101101001011", "100010111111001", "100000011001110", "100111110010111", "100101010100000" },
	{ [0] = "011010101011111", "011000001101000", "011111100110001", "011101000000110", "010010010110100", "010000110000011", "010111011011010", "010101111101101" },
	{ [0] = "001011010001001", "001001110111110", "001110011100111", "001100111010000", "000011101100010", "000001001010101", "000110100001100", "000100000111011" }
}

local function add_typeinfo_to_matrix(matrix, size, ec_level, mask)
	local ec_mask_type = typeinfo[ec_level][mask]
	local bit_val
	for i = 1, 7 do
		bit_val = sub(ec_mask_type, i, i) == "1" and 2 or -2
		set_cell(matrix, size, 9, size - i + 1, bit_val)
	end
	for i = 8, 9 do
		bit_val = sub(ec_mask_type, i, i) == "1" and 2 or -2
		set_cell(matrix, size, 9, 17 - i, bit_val)
	end
	for i = 10, 15 do
		bit_val = sub(ec_mask_type, i, i) == "1" and 2 or -2
		set_cell(matrix, size, 9, 16 - i, bit_val)
	end
	for i = 1, 6 do
		bit_val = sub(ec_mask_type, i, i) == "1" and 2 or -2
		set_cell(matrix, size, i, 9, bit_val)
	end
	bit_val = sub(ec_mask_type, 7, 7) == "1" and 2 or -2
	set_cell(matrix, size, 8, 9, bit_val)
	for i = 8, 15 do
		bit_val = sub(ec_mask_type, i, i) == "1" and 2 or -2
		set_cell(matrix, size, size - 15 + i, 9, bit_val)
	end
end

local version_information = {
	"001010010011111000", "001111011010000100", "100110010101100100", "110010110010010100",
	"011011111101110100", "010001101110001100", "111000100001101100", "101100000110011100", "000101001001111100",
	"000111101101000010", "101110100010100010", "111010000101010010", "010011001010110010", "011001011001001010",
	"110000010110101010", "100100110001011010", "001101111110111010", "001000110111000110", "100001111000100110",
	"110101011111010110", "011100010000110110", "010110000011001110", "111111001100101110", "101011101011011110",
	"000010100100111110", "101010111001000001", "000011110110100001", "010111010001010001", "111110011110110001",
	"110100001101001001", "011101000010101001", "001001100101011001", "100000101010111001", "100101100011000101",
}

local function add_version_information(matrix, version, size)
	if version < 7 then return end
	local bitstring = version_information[version - 6]
	local x, y, bit_val
	local start_x = size - 10
	local start_y = 1
	for i = 1, #bitstring do
		bit_val = sub(bitstring, i, i) == "1" and 2 or -2
		x = start_x + (i - 1) % 3
		y = start_y + floor((i - 1) / 3)
		set_cell(matrix, size, x, y, bit_val)
	end
	start_x = 1
	start_y = size - 10
	for i = 1, #bitstring do
		bit_val = sub(bitstring, i, i) == "1" and 2 or -2
		x = start_x + floor((i - 1) / 3)
		y = start_y + (i - 1) % 3
		set_cell(matrix, size, x, y, bit_val)
	end
end

local maskFunc = {
	[0]=function(x,y) return (y+x)%2==0 end,
	function(_,y) return y%2==0 end,
	function(x,_) return x%3==0 end,
	function(x,y) return (y+x)%3==0 end,
	function(x,y) return (y%4-1.5)*(x%6-2.5)>0 end,
	function(x,y) return (y*x)%2+(y*x)%3==0 end,
	function(x,y) return ((y*x)%3+y*x)%2==0 end,
	function(x,y) return ((y*x)%3+y+x)%2==0 end,
}

local function calculate_penalty(matrix, size)
	local penalty1, penalty2, penalty3 = 0, 0, 0
	local number_of_dark_cells = 0

	-- 1. Horizontal runs & Dark Cells (bounds: 1 to size)
	local row_offset = 0
	for y = 1, size do
		local consec_h = 0
		local last_c_h = nil
		for x = 1, size do
			local c = matrix[row_offset + x] > 0
			if c then number_of_dark_cells = number_of_dark_cells + 1 end

			if c == last_c_h then
				consec_h = consec_h + 1
			else
				if consec_h >= 5 then penalty1 = penalty1 + consec_h - 2 end
				consec_h = 1
				last_c_h = c
			end
		end
		if consec_h >= 5 then penalty1 = penalty1 + consec_h - 2 end
		row_offset = row_offset + size
	end

	-- 2. Vertical runs (bounds: 1 to size)
	for x = 1, size do
		local consec_v = 0
		local last_c_v = nil
		local idx = x
		for y = 1, size do
			local c = matrix[idx] > 0
			if c == last_c_v then
				consec_v = consec_v + 1
			else
				if consec_v >= 5 then penalty1 = penalty1 + consec_v - 2 end
				consec_v = 1
				last_c_v = c
			end
			idx = idx + size
		end
		if consec_v >= 5 then penalty1 = penalty1 + consec_v - 2 end
	end

	-- 3. 2x2 Blocks (bounds: 1 to size - 1)
	row_offset = 0
	for y = 1, size - 1 do
		for x = 1, size - 1 do
			local idx = row_offset + x
			local c1 = matrix[idx] > 0
			if c1 == (matrix[idx + 1] > 0) and c1 == (matrix[idx + size] > 0) and c1 == (matrix[idx + size + 1] > 0) then
				penalty2 = penalty2 + 3
			end
		end
		row_offset = row_offset + size
	end

	-- 4. 1:1:3:1:1 Pattern Horizontal (bounds: 1 to size - 6)
	row_offset = 0
	for y = 1, size do
		for x = 1, size - 6 do
			local idx = row_offset + x
			if matrix[idx] > 0 and matrix[idx+1] < 0 and matrix[idx+2] > 0 and matrix[idx+3] > 0 and matrix[idx+4] > 0 and matrix[idx+5] < 0 and matrix[idx+6] > 0 then
				if (x + 10 <= size and matrix[idx+7] < 0 and matrix[idx+8] < 0 and matrix[idx+9] < 0 and matrix[idx+10] < 0) or
				   (x >= 5 and matrix[idx-1] < 0 and matrix[idx-2] < 0 and matrix[idx-3] < 0 and matrix[idx-4] < 0) then
					penalty3 = penalty3 + 40
				end
			end
		end
		row_offset = row_offset + size
	end

	-- 5. 1:1:3:1:1 Pattern Vertical (bounds: 1 to size - 6)
	for x = 1, size do
		local idx = x
		for y = 1, size - 6 do
			if matrix[idx] > 0 and matrix[idx+size] < 0 and matrix[idx+size*2] > 0 and matrix[idx+size*3] > 0 and matrix[idx+size*4] > 0 and matrix[idx+size*5] < 0 and matrix[idx+size*6] > 0 then
				if (y + 10 <= size and matrix[idx+size*7] < 0 and matrix[idx+size*8] < 0 and matrix[idx+size*9] < 0 and matrix[idx+size*10] < 0) or
				   (y >= 5 and matrix[idx-size] < 0 and matrix[idx-size*2] < 0 and matrix[idx-size*3] < 0 and matrix[idx-size*4] < 0) then
					penalty3 = penalty3 + 40
				end
			end
			idx = idx + size
		end
	end

	-- Penalty 4: Dark/Light ratio
	local dark_ratio = number_of_dark_cells / (size * size)
	local penalty4 = floor(abs(dark_ratio * 100 - 50)) * 2

	return penalty1 + penalty2 + penalty3 + penalty4
end

-- Module-level scratchpads pre-allocated to Version 40 maximum size (177 * 177)
-- WARNING: Reusing these tables makes the qrcode() function non-reentrant.
-- It is safe for KOReader's single-threaded event loop, but must never be
-- invoked concurrently (e.g., via interleaved coroutines).
local MAX_QR_LEN = 31329
local base_matrix = {}
local best_matrix = {}
local scratch = {}
local free_idx = {}
local x_coords = {}
local y_coords = {}
local raw_bit = {}

for i = 1, MAX_QR_LEN do
	base_matrix[i] = 0
	best_matrix[i] = 0
	scratch[i] = 0
	free_idx[i] = 0
	x_coords[i] = 0
	y_coords[i] = 0
	raw_bit[i] = 0
end

local function generate_base_matrix(version)
	local size = version * 4 + 17
	local len = size * size

	for i = 1, len do
		base_matrix[i] = 0
	end

	for i = 1, 8 do
		for j = 1, 8 do
			set_cell(base_matrix, size, i, j, -2)
			set_cell(base_matrix, size, size - 8 + i, j, -2)
			set_cell(base_matrix, size, i, size - 8 + j, -2)
		end
	end

	for i = 1, 7 do
		set_cell(base_matrix, size, 1, i, 2); set_cell(base_matrix, size, 7, i, 2)
		set_cell(base_matrix, size, i, 1, 2); set_cell(base_matrix, size, i, 7, 2)
		set_cell(base_matrix, size, size, i, 2); set_cell(base_matrix, size, size - 6, i, 2)
		set_cell(base_matrix, size, size - i + 1, 1, 2); set_cell(base_matrix, size, size - i + 1, 7, 2)
		set_cell(base_matrix, size, 1, size - i + 1, 2); set_cell(base_matrix, size, 7, size - i + 1, 2)
		set_cell(base_matrix, size, i, size - 6, 2); set_cell(base_matrix, size, i, size, 2)
	end

	for i = 1, 3 do
		for j = 1, 3 do
			set_cell(base_matrix, size, 2 + j, i + 2, 2)
			set_cell(base_matrix, size, size - j - 1, i + 2, 2)
			set_cell(base_matrix, size, 2 + j, size - i - 1, 2)
		end
	end

	for i = 9, size - 8 do
		set_cell(base_matrix, size, i, 7, i % 2 == 0 and -2 or 2)
		set_cell(base_matrix, size, 7, i, i % 2 == 0 and -2 or 2)
	end

	add_version_information(base_matrix, version, size)
	set_cell(base_matrix, size, 9, size - 7, 2)

	local ap = alignment_pattern[version]
	for x = 1, #ap do
		for y = 1, #ap do
			if not (x == 1 and y == 1 or x == #ap and y == 1 or x == 1 and y == #ap) then
				local pos_x, pos_y = ap[x] + 1, ap[y] + 1
				for dy = -2, 2 do
					for dx = -2, 2 do
						set_cell(base_matrix, size, pos_x + dx, pos_y + dy, max(abs(dx), abs(dy)) % 2 == 0 and 2 or -2)
					end
				end
			end
		end
	end

	return size
end

local function qrcode(str, ec_level, mode_enc)
	local mode_num = mode_enc or get_mode(str)
	local version, ec = get_version_eclevel(#str, mode_num, ec_level)
	local bw = BitWriter.new()
	bw:write(mode_num, 4)
	write_length(bw, #str, version, mode_num)
	encode_data(str, mode_num, bw)
	local data_bytes = add_pad_data(version, ec, bw)
	local arranged_data = arrange_codewords_and_calculate_ec(version, ec, data_bytes)
	local size = generate_base_matrix(version)

	-- Reserve typeinfo cells so they are not treated as free data cells
	add_typeinfo_to_matrix(base_matrix, size, ec, 0)

	local len = size * size
	for i = 1, len do
		scratch[i] = base_matrix[i]
	end

	local free_count = 0
	local bit_idx = 0
	local total_bits = #arranged_data * 8

	local x, y = size, size
	local x_dir, y_dir = -1, -1

	while x >= 1 do
		local idx = (y - 1) * size + x
		if base_matrix[idx] == 0 then
			local data_bit = 0
			if bit_idx < total_bits then
				local byte_idx = floor(bit_idx / 8) + 1
				local b_shift = 7 - (bit_idx % 8)
				data_bit = band(rshift(arranged_data[byte_idx], b_shift), 1)
			end
			bit_idx = bit_idx + 1

			free_count = free_count + 1
			free_idx[free_count] = idx
			x_coords[free_count] = x - 1
			y_coords[free_count] = y - 1
			raw_bit[free_count] = data_bit
		end

		x = x + x_dir
		if x_dir == 1 then
			y = y + y_dir
			if y < 1 or y > size then
				x = x - 2
				if x == 7 then x = 6 end
				y = y_dir == -1 and 1 or size
				y_dir = -y_dir
			end
		end
		x_dir = -x_dir
	end

	local min_penalty = nil
	local best_mask = 0

	for mask = 0, 7 do
		add_typeinfo_to_matrix(scratch, size, ec, mask)

		local func = maskFunc[mask]
		for k = 1, free_count do
			local invert = func(x_coords[k], y_coords[k])
			local data_bit = raw_bit[k]
			if invert then data_bit = bxor(data_bit, 1) end
			scratch[free_idx[k]] = data_bit == 1 and 1 or -1
		end

		local penalty = calculate_penalty(scratch, size)
		if not min_penalty or penalty < min_penalty then
			min_penalty = penalty
			best_mask = mask
		end
	end

	-- Build the final matrix exactly once
	for i = 1, len do best_matrix[i] = base_matrix[i] end
	add_typeinfo_to_matrix(best_matrix, size, ec, best_mask)

	local func = maskFunc[best_mask]
	for k = 1, free_count do
		local invert = func(x_coords[k], y_coords[k])
		local data_bit = raw_bit[k]
		if invert then data_bit = bxor(data_bit, 1) end
		best_matrix[free_idx[k]] = data_bit == 1 and 1 or -1
	end

	return true, best_matrix, size
end

return {
    qrcode = qrcode
}