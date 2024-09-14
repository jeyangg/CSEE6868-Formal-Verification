`timescale 1ns / 1ps

// Combine 4 x o_mem to ofmap_mem
module OutputMemory
#(
    parameter INIT_FILE_NAME                    = ""  
)
(
   input  logic                                 clock,
   input  logic [9:0]                           rdaddress,
   output logic [511:0]                         rdata_out,
   input  logic                                 we_in,
   input  logic [9:0]                           wraddress,
   input  logic [511:0]                         wdata_in
);

    logic [3:0][127:0]                          o_data;
    logic [3:0][127:0]                          o_q;

    always_comb begin
        o_data                                  = wdata_in;
        rdata_out                               = o_q;
    end

    BankedOutputMemory #(
        .RAM_WIDTH                              (128),
        .RAM_ADDR_BITS                          (10),
        .INIT_FILE_NAME                         (INIT_FILE_NAME)
    )
    ofmap_mem0
    (
        .clk                                   (clock),            
        .raddr_in                              (rdaddress),                
        .rdata_out                             (o_q[0]),        
        .we_in                                 (we_in),            
        .waddr_in                              (wraddress),                
        .wdata_in                              (o_data[0])            
    );

    BankedOutputMemory #(
        .RAM_WIDTH                              (128),
        .RAM_ADDR_BITS                          (10),
        .INIT_FILE_NAME                         (INIT_FILE_NAME)
    )
    ofmap_mem1
    (
        .clk                                   (clock),            
        .raddr_in                              (rdaddress),                
        .rdata_out                             (o_q[1]),        
        .we_in                                 (we_in),            
        .waddr_in                              (wraddress),                
        .wdata_in                              (o_data[1])            
    );

    BankedOutputMemory #(
        .RAM_WIDTH                              (128),
        .RAM_ADDR_BITS                          (10),
        .INIT_FILE_NAME                         (INIT_FILE_NAME)
    )
    ofmap_mem2
    (
        .clk                                   (clock),            
        .raddr_in                              (rdaddress),                
        .rdata_out                             (o_q[2]),        
        .we_in                                 (we_in),            
        .waddr_in                              (wraddress),                
        .wdata_in                              (o_data[2])            
    );

    BankedOutputMemory #(
        .RAM_WIDTH                              (128),
        .RAM_ADDR_BITS                          (10),
        .INIT_FILE_NAME                         (INIT_FILE_NAME)
    )
    ofmap_mem3
    (
        .clk                                   (clock),            
        .raddr_in                              (rdaddress),                
        .rdata_out                             (o_q[3]),        
        .we_in                                 (we_in),            
        .waddr_in                              (wraddress),                
        .wdata_in                              (o_data[3])            
    );

endmodule