`timescale 1ns/1ps

module processor(clk, clearb, instO, pcO);
  input clk, clearb;
  output [31:0] instO, pcO;

  logic [31:0] imem [0:31];
  logic [31:0] dmem [0:31];
  
  logic zero, jump, branch, inreg, inALU, inDATA, enRF, enDM;
  logic [2:0] aluF;
  logic [31:0]aluOUT, pc, dmIN, inst, dmOUT;
  
  body b0(clk, inst, clearb, jump, branch, inreg, enRF, inALU, inDATA, dmOUT, aluF, pc, zero, aluOUT, dmIN);
  controlunit c0(inst[31:26], inst[5:0], zero, jump, branch, inreg, enRF, inALU, inDATA, enDM, aluF);

  initial begin
    $readmemb("imem.dat", imem); 
  end
  
  always@(posedge clk) begin
    if(enDM)
      dmem[aluOUT] <= dmIN;
  end

  assign dmOUT = dmem[aluOUT];
  assign inst = imem[pc>>2];

  assign instO = inst;
  assign pcO = pc;

  always@(*)
    if(inst[31:26] == 6'b111111) begin
      $writememb("RAMa.dat", dmem);
    end

endmodule

module body(clk, inst, clearb, jump, branch, inreg, enRF, inALU, inDATA, dmOUT, aluF, pc, zero, aluOUT, dmIN);
  input clk, clearb, jump, branch, inreg, enRF, inALU, inDATA; input [31:0] inst, dmOUT; input [2:0] aluF;
  output [31:0] pc, aluOUT, dmIN; output zero;
  
  logic [4:0] rs,rt,rd,r2;
  logic co;
  logic [31:0] data, out0, out1, b, pcp4, pcpb, immd, dpc0, dpc1, imjc, imds;
  logic [27:0] imj;
  
  assign rt = inst[20:16];
  assign rs = inst[25:21];
  assign rd = inst[15:11];
  
  regfile rf0(clk, rs, rt, r2, data, clearb, enRF, out0, out1);
  
  alu a0(out0, b, aluF, aluOUT, zero);
  
  dff rpc(clk, clearb, dpc1, pc);
  
  assign imj = {inst[25:0], 2'b00};
  assign imjc = {dpc0[31:28], imj};
  
  mux2to1 #(32) m0 (dpc0, imjc, jump, dpc1);
  mux2to1 #(32) m1 (pcp4, pcpb, branch, dpc0);
  
  mux2to1 #(5) m2 (rt, rd, inreg, r2);
  
  mux2to1 #(32) m3 (immd, out1, inALU, b);
  mux2to1 #(32) m4 (aluOUT, dmOUT, inDATA, data);
  
  signe a4(inst[15:0], immd);
  
  sl2 a3(immd, imds);
  
  add4 a1(pc, pcp4);
  faddc #(32) a2(pcp4, imds, 1'b0, pcpb, co);
  
  assign dmIN = out1;  
endmodule

module controlunit(op, func, zero, jump, branch, inreg, enRF, inALU, inDATA, enDM, aluF);
  input [5:0] op, func; input zero;
  output jump, branch, inreg, enRF, inALU, inDATA, enDM; output [2:0] aluF;
  
  logic sop, beq, bne;
  logic [2:0] si, s;
  
  assign sop = ~(|op);
  
  assign jump = ~(op[5])&~(op[3])&op[1];
  assign beq = (~op[3]) & (~op[1]) & (~op[0]);
  assign bne = (~op[3]) & (op[0]);
  assign branch = (( beq & zero) | ( bne & ~(zero))) & ~(sop);
  
  assign s[2] = (func[1]&func[0]) | ((~func[2]) & func[1] & (~func[0]));
  assign s[1] = func[0] | (func[2] & func[1]);
  assign s[0] = (func[2] & (~func[0])) | func[3];
  
  assign si[2] = ((~op[3]) & (~op[1])) | (op[3]&(~op[2])&op[1]&(~op[0]));
  assign si[1] = (op[2] & op[1]) | (op[3] & (~op[1]) & op[0]);
  assign si[0] = (op[3]&op[2]&(~op[0])) | (op[3]&op[1]&(~op[0]));
  
  mux2to1 #(3) m0(si, s, sop, aluF);
  
  assign enRF = ~(((~op[5]) & (~op[3])) | ((~op[2]) & op[0])) | sop;
  assign enDM = op[5] & (~op[4]) & op[3] & (~op[2]) & op[1] & op[0];
  
  assign inreg = sop | beq | bne;
  assign inALU = sop | beq | bne;
  assign inDATA = op[5] & (~op[4]) & (~op[3]) & (~op[2]) & op[1] & (~op[0]); 
endmodule

module dff(clk, clearb, d, q);
  
  input clk, clearb;
  input [31:0]d;
  output [31:0]q;
  
  logic [31:0]a0, a1, b0, b1, c0, c1, nq;
  logic clkn, presetb;
  assign presetb = 1'b1;
  
  assign clkn = ~clk;
  
  assign a0 = ~( d & {32{clkn}});
  assign a1 = ~( ~(d) & {32{clkn}});
  
  assign b0 = ~( b1 & {32{presetb}} & a0);
  assign b1 = ~( b0 & {32{clearb}} & a1);
  
  assign c0 = ~( b0 & {32{~(clkn)}});
  assign c1 = ~( b1 & {32{~(clkn)}});
  
  assign q = ~( c0 & {32{presetb}} & nq);
  assign nq = ~( c1 & {32{clearb}} & q); 
endmodule

module regfile(clk, r0, r1, r2, data, clearb, en, outr0, outr1);
  input [4:0] r0,r1,r2; input clk, clearb, en; input [31:0]data;
  output [31:0] outr0, outr1;
  
  // logic [31:0] outd;
  // logic [(32*32)-1:0] qC;

  // d5t32 d0(r2, outd);
  
  // genvar i;
  
  // generate
  //   for(i = 0; i<32; i = i + 1)begin
  //     dff regs(clk & en & outd[i], 1'b1, i==0?32'h00000000:data, qC[(i*32)+:32]);
  //   end
  // endgenerate
  
  // mux32to1c #(32) m0 (qC, r0, outr0);
  // mux32to1c #(32) m1 (qC, r1, outr1);

  logic [31:0] registers [31:0];

  always@(posedge clk) begin
    if(en & (r2!=5'b0))
      registers[r2] <= data;
  end

  assign outr0 = r0==5'b0 ? 32'd0 : registers[r0];
  assign outr1 = r1==5'b0 ? 32'd0 : registers[r1];
endmodule

module d2t4(i, out);
  input [1:0]i;
  output [3:0]out;
  
  assign out[0] = ~i[0] & ~i[1];
  assign out[1] = i[0] & ~i[1];
  assign out[2] = ~i[0] &  i[1];
  assign out[3] = i[0] & i[1];
endmodule

module d3t8(i, out);
  input [2:0]i;
  output [7:0]out;
  
  logic [3:0] od0;
  logic [7:0] out0, out1;
  
  d2t4 d0(i[1:0], od0);
  
  assign out0 = {4'h0, od0};
  assign out1 = {od0, 4'h0};
  
  mux2to1c #(8) m0 ({out1,out0}, i[2], out);
endmodule

module d4t16(i, out);
  input [3:0]i;
  output [15:0]out;
  
  logic [7:0] od0;
  logic [15:0] out0, out1;
  
  d3t8 d0(i[2:0], od0);
  
  assign out0 = {8'h00, od0};
  assign out1 = {od0, 8'h00};
  
  mux2to1c #(16) m0 ({out1, out0}, i[3], out);
endmodule

module d5t32(i, out);
  input [4:0]i;
  output [31:0]out;
  
  logic [15:0] od0;
  logic [31:0] out0, out1;
  
  d4t16 d0(i[3:0], od0);
  
  assign out0 = {16'h0000, od0};
  assign out1 = {od0, 16'h0000};
  
  mux2to1c #(32) m0 ({out1, out0}, i[4], out);
endmodule

module mux2to1 (i0, i1, s, out);
  parameter n=1;
  input [n-1:0]i0,i1; input s;
  output [n-1:0]out;
  
  logic [n-1:0] a0,a1;
  
  assign a0 = i0 & ~({n{s}});
  assign a1 = i1 & {n{s}};
  
  assign out = a0 | a1;
endmodule

module mux2to1c (i, s, out);
  parameter n=1;
  
  input [(n*2)-1:0]i; input s;
  output [n-1:0]out;
  
  mux2to1 #(n) m0(i[(n*1)-1-:n], i[(n*2)-1-:n], s, out); 
endmodule

module mux4to1c(i, s, out);
  parameter n=1;
  
  input [(n*4)-1:0]i; input [1:0]s;
  output [n-1:0]out;  
  
  logic [n-1:0] out0, out1;
  
  mux2to1 #(n) m0(i[(n*1)-1-:n], i[(n*2)-1-:n], s[0], out0);
  mux2to1 #(n) m1(i[(n*3)-1-:n], i[(n*4)-1-:n], s[0], out1);
  
  mux2to1 #(n) m2(out0, out1, s[1], out);
endmodule

module mux8to1c(i, s, out);
  parameter n=1;
  
  input [(n*8)-1:0]i; input [2:0]s;
  output [n-1:0]out;  
 
  logic [n-1:0] out0, out1;
  
  mux4to1c #(n) m0(i[(n*4)-1-:(n*4)], s[1:0], out0);
  mux4to1c #(n) m1(i[(n*8)-1-:(n*4)], s[1:0], out1);
  
  mux2to1 #(n) m2(out0, out1, s[2], out); 
endmodule

module mux16to1c(i, s, out);
  parameter n=1;
  
  input [(n*16)-1:0]i; input [3:0]s;
  output [n-1:0]out;  
 
  logic [n-1:0] out0, out1;
  
  mux8to1c #(n) m0(i[(n*8)-1-:(n*8)], s[2:0], out0);
  mux8to1c #(n) m1(i[(n*16)-1-:(n*8)], s[2:0], out1);
  
  mux2to1 #(n) m2(out0, out1, s[3], out); 
endmodule

module mux32to1c(i, s, out);
  parameter n=1;
  
  input [(n*32)-1:0]i; input [4:0]s;
  output [n-1:0]out;  
 
  logic [n-1:0] out0, out1;
  
  mux16to1c #(n) m0(i[(n*16)-1-:(n*16)], s[3:0], out0);
  mux16to1c #(n) m1(i[(n*32)-1-:(n*16)], s[3:0], out1);
  
  mux2to1 #(n) m2(out0, out1, s[4], out);
endmodule

module fadd( a, b, ci, s, co);
  input a,b,ci;
  output s,co;
  
  logic a0,a1,b0;
  
  assign a0 = a^b;
  assign a1 = a&b;
  assign s = a0^ci;
  assign b0 = a0&ci;
  assign co = a1 | b0;
endmodule

module faddc ( a, b, ci, s, co);
  parameter n=1;
  input [n-1:0]a,b; input ci;
  output [n-1:0]s; output co;

  logic [n-1:0] carry;
  
  genvar i;
  
  generate
    for(i = 0 ; i < n ; i = i + 1 ) begin
      fadd fa( a[i], b[i], i==0?ci:carry[i-1], s[i], carry[i]);
    end
  endgenerate
  
  assign co = carry[31];
endmodule

module add4(i, out);
  input [31:0]i;
  output [31:0]out;
  assign out = i+4;
endmodule

module sl2 (i,o);
  input[31:0]i;
  output[31:0]o;
  
  assign o = {i[29:0], 2'b00};
endmodule

module signe (i,o);
  input[15:0]i;
  output[31:0]o;
  
  assign o = {{16{i[15]}}, i};
endmodule

module sumsubc(a, b, pb_m, res, cout);
  input [31:0] a,b; input pb_m;
  output [31:0] res; output cout;
  
  logic [31:0] bM;
  
  mux2to1 #(32) m0 (b, ~(b), pb_m, bM);
  
  faddc #(32) f0 (a, bM, pb_m, res, cout);
endmodule

module alu (a, b, s, aluOUT, zero);
  input [31:0] a,b; input [2:0]s;
  output [31:0]aluOUT; output zero;
  
  logic [31:0] res, outand, outor, outnor, outxor, outm0, outm1, outm2;
  logic cout;
  
  sumsubc ss0(a,b,s[2], res, cout);
  
  assign outand = a & b;
  assign outor = a | b;
  assign outnor = ~outor;
  assign outxor = a ^ b;
  
  mux2to1 #(32) m0 (outand, {{31{1'b0}},res[31]}, s[2], outm0);
  mux2to1 #(32) m1 (outor, outnor, s[2], outm1);
  
  mux4to1c #(32) m2({outxor,outm1, outm0, res}, s[1:0], outm2);
  
  assign aluOUT = outm2;
  assign zero = ~(|outm2);
endmodule