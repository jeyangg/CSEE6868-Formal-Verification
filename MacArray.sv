`timescale 1 ns / 1 ps

module MacArray
#(
    parameter MAC_ROW                                                   = 16,
    parameter MAC_COL                                                   = 16,
    parameter IFMAP_BITWIDTH                                            = 16,
    parameter W_BITWIDTH                                                = 8,
    parameter OFMAP_BITWIDTH                                            = 32
)
(
    input  logic                                                        clk,
    input  logic                                                        rstn,

    input  logic                                                        w_prefetch_in,
    input  logic                                                        w_enable_in,
    input  logic [MAC_COL-1:0][W_BITWIDTH-1:0]                          w_data_in,

    input  logic                                                        ifmap_start_in,
    input  logic [MAC_ROW-1:0]                                          ifmap_enable_in,
    input  logic [MAC_ROW-1:0][IFMAP_BITWIDTH-1:0]                      ifmap_data_in,

    output logic [MAC_COL-1:0]                                          ofmap_valid_out,
    output logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]                      ofmap_data_out
);

    logic [MAC_ROW-1:0][MAC_COL-1:0][W_BITWIDTH-1:0]                    mac_w_data_in;
    logic [MAC_COL-1:0][MAC_ROW-1:0]                                    mac_ifmap_enable_in;
    logic [MAC_COL-1:0][MAC_ROW-1:0][IFMAP_BITWIDTH-1:0]                mac_ifmap_data_in;
    logic [MAC_ROW-1:0][MAC_COL-1:0][OFMAP_BITWIDTH-1:0]                mac_psum_data_in;

    logic [MAC_ROW-1:0][MAC_COL-1:0][W_BITWIDTH-1:0]                    mac_w_data_out;
    logic [MAC_COL-1:0][MAC_ROW-1:0]                                    mac_ifmap_enable_out;
    logic [MAC_COL-1:0][MAC_ROW-1:0][IFMAP_BITWIDTH-1:0]                mac_ifmap_data_out;
    logic [MAC_ROW-1:0][MAC_COL-1:0][OFMAP_BITWIDTH-1:0]                mac_psum_data_out;

    assign ofmap_data_out                                               = mac_psum_data_out[MAC_ROW-1];
    assign mac_w_data_in[0]                                             = w_data_in;
    assign mac_ifmap_enable_in[0]                                       = ifmap_enable_in;
    assign mac_ifmap_data_in[0]                                         = ifmap_data_in; 
    assign mac_psum_data_in[0]                                          = 0;
    
    genvar m;
    generate
        for (m = 0; m < MAC_COL; m++) begin : valid_out
            assign ofmap_valid_out[m]                                   = mac_ifmap_enable_out[m][MAC_ROW-1]; 
        end
    endgenerate

    genvar i;
    generate
        for (i = 1; i < MAC_ROW; i++) begin : wire_row
            assign mac_w_data_in[i]                                     = mac_w_data_out[i-1];
            assign mac_psum_data_in[i]                                  = mac_psum_data_out[i-1];
        end
    endgenerate

    genvar j;
    generate
        for (j = 1; j < MAC_COL; j++) begin : wire_col
            assign mac_ifmap_enable_in[j]                               = mac_ifmap_enable_out[j-1];
            assign mac_ifmap_data_in[j]                                 = mac_ifmap_data_out[j-1];   
        end
    endgenerate

    genvar k, l;
    generate
        for (k = 0; k < MAC_ROW; k++) begin : mac_row
            for (l = 0; l < MAC_COL; l++) begin : mac_col
                Mac
                #(
                    .IFMAP_BITWIDTH                                     (IFMAP_BITWIDTH),
                    .W_BITWIDTH                                         (W_BITWIDTH),
                    .OFMAP_BITWIDTH                                     (OFMAP_BITWIDTH)
                )
                mac
                (
                    .clk                                                (clk),
                    .rstn                                               (rstn),

                    .w_enable_in                                        (w_enable_in),
                    .w_data_in                                          (mac_w_data_in[k][l]),
                    .ifmap_enable_in                                    (mac_ifmap_enable_in[l][k]),
                    .ifmap_data_in                                      (mac_ifmap_data_in[l][k]),
                    .psum_data_in                                       (mac_psum_data_in[k][l]),

                    .w_data_out                                         (mac_w_data_out[k][l]),
                    .ifmap_enable_out                                   (mac_ifmap_enable_out[l][k]),
                    .ifmap_data_out                                     (mac_ifmap_data_out[l][k]),
                    .psum_data_out                                      (mac_psum_data_out[k][l])
                );
            end
        end
    endgenerate

endmodule