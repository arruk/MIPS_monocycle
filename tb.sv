`timescale 1ns/1ps

`include "core.sv"

module tb;

    reg clk, clearb;
    reg [31:0] inst, pc;

    integer i;

    always begin
        clk=0; #5; clk=1; #5;
    end

    initial begin
        i=0;
        clearb=1'b0; #10; clearb=1'b1;
        $display("inicializando o testbench");
        $dumpfile("dump.vcd"); $dumpvars;
    end

    processor dut (clk, clearb, inst , pc);

    always@(posedge clk) begin
        i++;
        if(inst[31:26] == 6'b111111 || i == 20) begin
            $display("finalizando o testbench");
            $finish();
        end
    end
endmodule