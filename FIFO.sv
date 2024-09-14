`timescale 1ns / 1ps

module FIFO
#(
    parameter DATA_WIDTH                = 32,
    parameter LOG_DEPTH                 = 4,
    parameter FIFO_DEPTH                = 2**LOG_DEPTH
)   
(   
    input  wire                         clk,
    input  wire                         rstn,
    input  wire                         wrreq,         // write request
    input  wire                         rdreq,         // Read request
    input  wire  [DATA_WIDTH-1:0]       data,          // Write data
    output logic [DATA_WIDTH-1:0]       q,             // Read data
    output logic                        full,          // Full status signal
    output logic                        empty          // Empty status signal
);

    logic [DATA_WIDTH-1:0]              mem[FIFO_DEPTH-1:0];

    struct packed {
        logic [LOG_DEPTH:0]             count;
        logic [LOG_DEPTH-1:0]           readcounter;
        logic [LOG_DEPTH-1:0]           writecounter;
    } regs_ff, regs_nxt;
    
    assign empty                        = ~|regs_ff.count;
    assign full                         = (regs_ff.count == FIFO_DEPTH);
    assign q                            = mem[regs_ff.readcounter];

    always_comb begin
        regs_nxt                        = regs_ff;
        if (rdreq) begin
            regs_nxt.readcounter        = regs_ff.readcounter+'d1;
        end
        if (wrreq) begin
            regs_nxt.writecounter       = regs_ff.writecounter+'d1;
        end
        if (rdreq&~wrreq) begin
            regs_nxt.count              = regs_ff.count-'d1;
        end
        else if (wrreq&~rdreq) begin
            regs_nxt.count              = regs_ff.count+'d1;
        end
    end

    always_ff @(posedge clk) begin
        if(~rstn) begin
            regs_ff                                             <= 'd0;
        end
        else begin
            regs_ff                                             <= regs_nxt;
            if (wrreq) begin
                mem[regs_ff.writecounter]                       <= data;
            end
        end
    end

endmodule