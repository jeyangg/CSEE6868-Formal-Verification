`timescale 1ns / 1ps

module SinglePortRam
#(
    parameter RAM_WIDTH                     = 32,
    parameter RAM_ADDR_BITS                 = 10,
    parameter INIT_FILE_NAME                = ""  
)(          
    input   logic                           rstn, //Added by Mao for Equivalence Checking
    input   logic                           clk,
    input   logic                           we_in,
    input   logic [RAM_ADDR_BITS-1:0]       addr_in,
    input   logic [RAM_WIDTH-1:0]           wdata_in,
    output  logic [RAM_WIDTH-1:0]           rdata_out
);
    reg [RAM_WIDTH-1:0]                   mem[(2**RAM_ADDR_BITS)-1:0];
    
    initial begin
        if (INIT_FILE_NAME != "") begin
            $readmemh(INIT_FILE_NAME, mem);
        end
    end

    always @(posedge clk) begin

        if (we_in) begin
            mem[addr_in]        <= wdata_in;
        end
        else begin
            rdata_out           <= mem[addr_in];
        end
    end

endmodule

module BankedOutputMemory
#(
    parameter RAM_WIDTH                     = 32,
    parameter RAM_ADDR_BITS                 = 10,
    parameter INIT_FILE_NAME                = ""  
)(          
    input   logic                           clk,
    input   logic [RAM_ADDR_BITS-1:0]       raddr_in,
    output  logic [RAM_WIDTH-1:0]           rdata_out,
    input   logic                           we_in,
    input   logic [RAM_ADDR_BITS-1:0]       waddr_in,
    input   logic [RAM_WIDTH-1:0]           wdata_in
);
    reg [RAM_WIDTH-1:0]                   mem[(2**RAM_ADDR_BITS)-1:0];

    initial begin
        if (INIT_FILE_NAME != "") begin
            $readmemh(INIT_FILE_NAME, mem);
        end
    end

    always @(posedge clk) begin
        if (we_in) begin
            mem[waddr_in]       <= wdata_in;
        end
        else begin
            rdata_out           <= mem[raddr_in];
        end
    end

endmodule
