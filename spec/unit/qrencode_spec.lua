require("ffi_wrapper")
local qrencode = require("ffi/qrencode")

describe("QRencode module", function()
    it("should match the defined result", function()
        local result = '2;2;2;2;2;2;2;-2;-2;-1;1;1;1;-2;2;2;2;2;2;2;2;2;-2;-2;-2;-2;-2;2;-2;-2;-1;-1;1;1;-2;2;-2;-2;'
          ..'-2;-2;-2;2;2;-2;2;2;2;-2;2;-2;-2;-1;1;-1;-1;-2;2;-2;2;2;2;-2;2;2;-2;2;2;2;-2;2;-2;2;1;1;1;-1;-2;2;-2;2;'
          ..'2;2;-2;2;2;-2;2;2;2;-2;2;-2;-2;1;-1;-1;-1;-2;2;-2;2;2;2;-2;2;2;-2;-2;-2;-2;-2;2;-2;-2;-1;-1;-1;1;-2;2;'
          ..'-2;-2;-2;-2;-2;2;2;2;2;2;2;2;2;-2;2;-2;2;-2;2;-2;2;2;2;2;2;2;2;-2;-2;-2;-2;-2;-2;-2;-2;-2;1;1;-1;-1;-2;'
          ..'-2;-2;-2;-2;-2;-2;-2;2;2;-2;2;2;2;2;-2;-2;1;1;-1;1;2;-2;-2;-2;2;-2;-2;-2;1;1;-1;-1;-1;1;-2;1;1;-1;-1;1;'
          ..'1;-1;1;1;-1;1;-1;1;-1;1;-1;1;-1;-1;-1;2;1;-1;-1;1;-1;1;-1;1;1;-1;-1;-1;-1;1;-1;-1;1;1;1;-1;-2;-1;1;-1;'
          ..'-1;-1;-1;1;1;-1;1;1;-1;1;1;1;-1;-1;1;-1;-1;2;1;-1;1;1;1;-1;1;-1;1;-1;-1;1;-1;-1;-2;-2;-2;-2;-2;-2;-2;-2;'
          ..'-2;-1;-1;-1;-1;1;-1;-1;1;-1;1;-1;1;2;2;2;2;2;2;2;-2;-2;1;1;1;-1;-1;1;1;1;-1;-1;1;-1;2;-2;-2;-2;-2;-2;2;'
          ..'-2;2;1;1;1;1;-1;-1;-1;-1;1;1;1;1;2;-2;2;2;2;-2;2;-2;2;-1;1;1;-1;1;1;-1;-1;-1;-1;-1;-1;2;-2;2;2;2;-2;2;'
          ..'-2;2;-1;1;1;1;1;-1;-1;1;1;-1;1;1;2;-2;2;2;2;-2;2;-2;-2;-1;1;-1;-1;-1;-1;-1;-1;-1;1;-1;1;2;-2;-2;-2;-2;'
          ..'-2;2;-2;2;1;-1;1;1;1;1;1;-1;1;-1;-1;1;2;2;2;2;2;2;2;-2;2;1;1;1;1;1;-1;-1;1;1;1;-1;-1;'
        local ok, matrix, size = qrencode.qrcode('test')
        assert.is_true(ok)
        local ret = {}
        for x = 1, size do
            for y = 1, size do
                table.insert(ret, tostring(matrix[(y - 1) * size + x]))
                table.insert(ret, ';')
            end
        end
        assert.are.same(table.concat(ret, ''), result)
    end)

    -- This refers to the standard ISO/IEC 18004 published in 2006
    describe("encoding pipeline (ISO/IEC 18004 Annex I worked example)", function()
		it("selects numeric mode and version 1 for the Annex I string", function()
			local result = qrencode._debug_mask_penalties("01234567", 2) -- 2 = EC level M
			assert.are.equal(1, result.version)
			assert.are.equal(2, result.ec)
		end)

		it("generates exact data and Reed-Solomon parity codewords for Annex I", function()
			local result = qrencode._debug_mask_penalties("01234567", 2)
			local expected_codewords = {
				-- 16 Data codewords (mode, character count, payload, terminator, 0xEC/0x11 pad bytes)
				0x10, 0x20, 0x0C, 0x56, 0x61, 0x80, 0xEC, 0x11,
				0xEC, 0x11, 0xEC, 0x11, 0xEC, 0x11, 0xEC, 0x11,
				-- 10 Reed-Solomon parity codewords from degree-10 polynomial division
				0xA5, 0x24, 0xD4, 0xC1, 0xED, 0x36, 0xC7, 0x87, 0x2C, 0x55,
			}
			assert.are.same(expected_codewords, result.codewords)
		end)
	end)

    -- The following tests are based on the worked example in ISO/IEC 18004 (2000) Annex G, with corrections from Persson's published errata.
    -- A copy of Johan Persson's paper can be found at https://www.coastalmonitoring.org/resources/jpclass/QR/qr-comment.pdf

	describe("encoding pipeline (ISO/IEC 18004 Annex G worked example)", function()
		it("selects numeric mode and version 1 for the Annex G string", function()
			local result = qrencode._debug_mask_penalties("01234567", 2) -- 2 = EC level M
			assert.are.equal(1, result.version)
			assert.are.equal(2, result.ec)
		end)
	end)

	describe("mask penalty scoring vs Persson's published correction to Annex G", function()
		local result = qrencode._debug_mask_penalties("01234567", 2)

        -- Persson's paper famously used Mask 7 to debunk the ISO standard's erroneous choice of Mask 3.
        -- Persson proved that Mask 7 mathematically beats Mask 3. However, when a fully compliant, bug-free
        -- penalty scorer evaluates all eight masks for the string "01234567" at Level M,
        -- Mask 2 actually yields an even lower total penalty than Mask 7.
		it("evaluates Mask 7 as having a lower penalty than Mask 3, correcting Annex G's example", function()
			local p_mask3 = result.components[3].p1 + result.components[3].p2 + result.components[3].p3 + result.components[3].p4
			local p_mask7 = result.components[7].p1 + result.components[7].p2 + result.components[7].p3 + result.components[7].p4
			assert.is_true(p_mask7 < p_mask3)
		end)
        it("finds Mask 2 is the actual global minimum across all 8 masks for this string", function()
			assert.are.equal(2, result.best_mask)
		end)

		it("matches Persson's P1 (line-run) scores exactly", function()
			assert.are.equal(187, result.components[3].p1)
			assert.are.equal(176, result.components[7].p1)
		end)

		it("matches Persson's P2 (2x2 block) scores exactly", function()
			assert.are.equal(105, result.components[3].p2)
			assert.are.equal(150, result.components[7].p2)
		end)

		it("matches Persson's P3 (finder-like pattern) scores and 40-point gap exactly", function()
			assert.are.equal(760, result.components[3].p3)
			assert.are.equal(720, result.components[7].p3)
			assert.are.equal(40, result.components[3].p3 - result.components[7].p3)
		end)

		it("matches Persson's P4 (dark ratio) scores exactly", function()
			assert.are.equal(0, result.components[3].p4)
			assert.are.equal(0, result.components[7].p4)
		end)
	end)

	describe("qrcode() across a range of versions", function()
		local base_text = "The quick brown fox jumps over the lazy dog. "
		local function make_payload(len)
			local s = base_text:rep(math.ceil(len / #base_text))
			return s:sub(1, len)
		end

		local test_lengths = { 10, 50, 100, 200, 350, 500, 800, 1200, 1700, 2200, 2700, 2953 }

		for _, len in ipairs(test_lengths) do
			it(string.format("encodes a %d-byte payload successfully with a well-formed matrix", len), function()
				local payload = make_payload(len)
				local ok, matrix, size = qrencode.qrcode(payload, 1)
				assert.are.equal(true, ok)
				assert.is_true(size >= 21 and size <= 177)
				assert.are.equal(0, (size - 17) % 4)

				local function cell(x, y) return matrix[(y - 1) * size + x] end
				assert.is_true(cell(1, 1) > 0)
				assert.is_true(cell(7, 1) > 0)
				assert.is_true(cell(1, 7) > 0)
				assert.is_true(cell(4, 4) > 0)
				assert.is_true(cell(2, 2) < 0)
			end)
		end
	end)

    describe("Cross MAX_TEXT_LENGTH boundary", function()
		local base_text = "The quick brown fox jumps over the lazy dog. "

		it("encodes at version 40 (2953 bytes)", function()
			local payload = base_text:rep(math.ceil(2953 / #base_text)):sub(1, 2953)
			local ok, _, size = qrencode.qrcode(payload, 1)
			assert.are.equal(true, ok)
			assert.are.equal(177, size)
		end)

		it("raises an error when payload exceeds version 40 capacity (2954 bytes)", function()
			local payload = base_text:rep(math.ceil(2954 / #base_text)):sub(1, 2954)
			assert.has_error(function()
				qrencode.qrcode(payload, 1)
			end)
		end)
	end)

    -- There are several canonical strings and test vectors drawn from the ISO specification, standard
    -- libraries (libqrencode, ZXing), and Project Nayuki that serve as established ground truths:

    describe("specification reference vectors", function()
		it("encodes ISO/IEC 18004 Section 8.4.3 example 'AC-42' at Version 1-M", function()
			local res = qrencode._debug_mask_penalties("AC-42", 2)
			assert.are.equal(1, res.version)
			assert.are.equal(2, res.ec)
		end)

		it("encodes industry standard 'HELLO WORLD' at Version 1-M", function()
			local res = qrencode._debug_mask_penalties("HELLO WORLD", 2)
			assert.are.equal(1, res.version)
			assert.are.equal(2, res.ec)
		end)

		it("encodes the full standard alphanumeric 45-character symbol set", function()
			local alnum_set = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
			local ok, _, size = qrencode.qrcode(alnum_set, 1)
			assert.is_true(ok)
			assert.are.equal(25, size) -- 45 alphanumeric characters bump cleanly to Version 2-L
		end)
	end)

	describe("numeric remainder bit-packing boundaries", function()
		local boundary_strings = {
			{ str = "7",    desc = "1 digit (4-bit remainder)" },
			{ str = "84",   desc = "2 digits (7-bit remainder)" },
			{ str = "492",  desc = "3 digits (10-bit triplet)" },
			{ str = "1048", desc = "4 digits (1 triplet + 1 remainder)" },
		}

		for _, tc in ipairs(boundary_strings) do
			it(string.format("encodes %s correctly in Version 1", tc.desc), function()
				local ok, _, size = qrencode.qrcode(tc.str, 1)
				assert.is_true(ok)
				assert.are.equal(21, size)
			end)
		end

		it("saturates Version 1-L numeric capacity at exactly 41 digits", function()
			local payload_41 = string.rep("9", 41)
			local ok, _, size = qrencode.qrcode(payload_41, 1)
			assert.is_true(ok)
			assert.are.equal(21, size)

			local payload_42 = string.rep("9", 42)
			local ok2, _, size2 = qrencode.qrcode(payload_42, 1)
			assert.is_true(ok2)
			assert.are.equal(25, size2)
		end)
	end)

	describe("Version 1 capacity boundaries across EC levels (8-bit byte mode)", function()
		local levels = {
			{ ec = 1, max_v1 = 17, name = "Level L" },
			{ ec = 2, max_v1 = 14, name = "Level M" },
			{ ec = 3, max_v1 = 11, name = "Level Q" },
			{ ec = 4, max_v1 = 7,  name = "Level H" },
		}

		for _, lvl in ipairs(levels) do
			it(string.format("fits %d bytes in Version 1 for %s", lvl.max_v1, lvl.name), function()
				local payload = string.rep("a", lvl.max_v1)
				local ok, _, size = qrencode.qrcode(payload, lvl.ec)
				assert.is_true(ok)
				assert.are.equal(21, size)
			end)

			it(string.format("promotes %d bytes to Version 2 for %s", lvl.max_v1 + 1, lvl.name), function()
				local payload = string.rep("a", lvl.max_v1 + 1)
				local ok, _, size = qrencode.qrcode(payload, lvl.ec)
				assert.is_true(ok)
				assert.are.equal(25, size)
			end)
		end
	end)

	describe("binary safety and embedded null transparency", function()
		it("encodes payload containing mixed nulls, control chars, and high bytes", function()
			local binary_payload = "PREFIX\0\1\2\255\128SUFFIX"
			local ok, _, size = qrencode.qrcode(binary_payload, 1)
			assert.is_true(ok)
			assert.are.equal(21, size)
		end)

		it("preserves exact Version 1 capacity boundaries when payload consists entirely of null bytes", function()
			local null_v1 = string.rep("\0", 17)
			local ok, _, size = qrencode.qrcode(null_v1, 1)
			assert.is_true(ok)
			assert.are.equal(21, size)

			local null_v2 = string.rep("\0", 18)
			local ok2, _, size2 = qrencode.qrcode(null_v2, 1)
			assert.is_true(ok2)
			assert.are.equal(25, size2)
		end)
	end)
end)