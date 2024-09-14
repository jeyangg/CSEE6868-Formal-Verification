`timescale 1 ns / 1 ps

module Systolic 
#(
    // logic parameter
    parameter MAC_ROW                           = 16,            // 16
    parameter MAC_COL                           = 16,            // 16
    parameter W_BITWIDTH                        = 8,
    parameter IFMAP_BITWIDTH                    = 16,
    parameter OFMAP_BITWIDTH                    = 32,
    parameter W_ADDR_BIT                        = 11,
    parameter IFMAP_ADDR_BIT                    = 9,
    parameter OFMAP_ADDR_BIT                    = 10,
    // operation parameter
    parameter OFMAP_CHANNEL_NUM                 = 16,       // 64
    parameter IFMAP_CHANNEL_NUM                 = 16,       // 32
    parameter WEIGHT_WIDTH                      = 3,
    parameter WEIGHT_HEIGHT                     = 3,
    parameter IFMAP_WIDTH                       = 4,        // 16
    parameter IFMAP_HEIGHT                      = 4,        // 16
    parameter OFMAP_WIDTH                       = 2,        // 14
    parameter OFMAP_HEIGHT                      = 2,        // 14
    // initialization data path
    parameter IFMAP_DATA_PATH                   = "",
    parameter WEIGHT_DATA_PATH                  = "",
    parameter OFMAP_DATA_PATH                   = ""
)
(
    input  logic                                clk,
    input  logic                                rstn,

    // do not modify this port: for verification at simulation
    input  logic [OFMAP_ADDR_BIT-1:0]           test_output_addr_in,
    input  logic                                test_check_in,
    output logic [MAC_COL*OFMAP_BITWIDTH-1:0]   test_output_out,

    input  logic                                start_in,

    output logic                                finish_out

);

    logic [MAC_COL-1:0][W_BITWIDTH-1:0]         w_data;
    logic [W_ADDR_BIT-1:0]                      w_addr;

    logic [MAC_ROW-1:0][IFMAP_BITWIDTH-1:0]     ifmap_data;
    logic [IFMAP_ADDR_BIT-1:0]                  ifmap_addr;

    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     ofmap_wdata;
    logic [OFMAP_ADDR_BIT-1:0]                  ofmap_addr;
    logic                                       ofmap_wen;

    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     psum_data;
    logic [OFMAP_ADDR_BIT-1:0]                  psum_addr;
    logic [OFMAP_ADDR_BIT-1:0]                  psum_addr_mux;

    // your code here

    logic                                       w_prefetch;
    logic                                       w_read_en;
    logic                                       w_enable;

    logic                                       ifmap_start;
    logic                                       ifmap_read_en;
    logic                                       ififo_write_en;
    logic [MAC_ROW-1:0]                         ififo_read_en;
    logic [MAC_ROW-1:0]                         ifmap_enable;
    logic [MAC_ROW-1:0][IFMAP_BITWIDTH-1:0]     ififo_data;

    logic                                       ofmap_ready;
    logic                                       ofifo_read_en;
    logic                                       ofmap_write_en;
    logic [MAC_COL-1:0]                         ofmap_valid;
    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     ofmap_data;
    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     ofifo_data;
    
    logic                                       ofmap_write_done;
    logic                                       mac_done;

    logic [9:0]                                 prop_i_state_cnt, i_state_cnt;
    logic [9:0]                                 prop_i_state_err, i_state_err;
    logic [9:0]                                 prop_w_state_cnt, w_state_cnt;
    logic [9:0]                                 prop_w_state_err, w_state_err;
    logic [9:0]                                 prop_o_state_cnt, o_state_cnt;
    logic [9:0]                                 prop_o_state_err, o_state_err;

    assign ifmap_enable                         = ififo_read_en;
    assign ofmap_ready                          = ofmap_valid[15];
    assign ofmap_wen                            = ofifo_read_en;
    assign start_in_toggle                      = (start_in == start_in_d1) ? 1'b0 : 1'b1;

    always_ff @(posedge clk) begin
        if(~rstn) begin
            start_in_d1                         <= '0;
            start_in_d1                         <= '0;
            finish_out                          <= '0;

            w_enable                            <= '0;
            ififo_write_en                      <= '0;
            ofifo_read_en                       <= '0;
            ofmap_addr                          <= '0;

            prop_i_state_cnt                    <= '0;
            prop_i_state_err                    <= '0;
            prop_w_state_cnt                    <= '0;
            prop_w_state_err                    <= '0;
            prop_o_state_cnt                    <= '0;
            prop_o_state_err                    <= '0;
        end
        else begin
            start_in_d1                         <= start_in;
            start_in_d2                         <= start_in_d1;
            finish_out                          <= ofmap_write_done;

            w_enable                            <= w_read_en;
            ififo_write_en                      <= ifmap_read_en;
            ofifo_read_en                       <= ofmap_valid[15];
            ofmap_addr                          <= psum_addr;

            prop_i_state_cnt                    <= i_state_cnt;
            prop_i_state_err                    <= i_state_err;
            prop_w_state_cnt                    <= w_state_cnt;
            prop_w_state_err                    <= w_state_err;
            prop_o_state_cnt                    <= o_state_cnt;
            prop_o_state_err                    <= o_state_err;
        end
    end

    genvar i;
    generate
        for (i = 0; i < MAC_ROW; i = i+1) begin: fifo_row
            FIFO #(
                .DATA_WIDTH                     (IFMAP_BITWIDTH),
                .LOG_DEPTH                      (4),
                .FIFO_DEPTH                     (2**4)
            ) if_fifo (   
                .clk                            (clk),
                .rstn                           (rstn),
                .wrreq                          (ififo_write_en),
                .rdreq                          (ififo_read_en[i]),
                .data                           (ifmap_data[15-i]),
                .q                              (ififo_data[i]),
                .full                           (/*unused*/),
                .empty                          (/*unused*/)
            );

            always_ff @(posedge clk) begin: fifo_row_signal
                if (i == 0) begin
                    ififo_read_en[0]            <= ififo_write_en;
                end
                else begin
                    ififo_read_en[i]            <= ififo_read_en[i-1];
                end 
            end
        end
    endgenerate

    genvar j;
    generate
        for (j = 0; j < MAC_COL; j = j+1) begin: fifo_col
            FIFO #(
                .DATA_WIDTH                     (OFMAP_BITWIDTH),
                .LOG_DEPTH                      (4),
                .FIFO_DEPTH                     (2**4)
            ) of_fifo (   
                .clk                            (clk),
                .rstn                           (rstn),
                .wrreq                          (ofmap_valid[j]),
                .rdreq                          (ofifo_read_en),
                .data                           (ofmap_data[j]),
                .q                              (ofifo_data[j]),
                .full                           (/*unused*/),
                .empty                          (/*unused*/)
            );
            assign ofmap_wdata[j]               = psum_data[j] + ofifo_data[j];
        end
    endgenerate

    MemoryController #(
        .MAC_ROW                                (MAC_ROW),
        .MAC_COL                                (MAC_COL),
        .W_BITWIDTH                             (W_BITWIDTH),
        .IFMAP_BITWIDTH                         (IFMAP_BITWIDTH),
        .OFMAP_BITWIDTH                         (OFMAP_BITWIDTH),
        .W_ADDR_BIT                             (W_ADDR_BIT),
        .IFMAP_ADDR_BIT                         (IFMAP_ADDR_BIT),
        .OFMAP_ADDR_BIT                         (OFMAP_ADDR_BIT),
        .OFMAP_CHANNEL_NUM                      (OFMAP_CHANNEL_NUM),
        .IFMAP_CHANNEL_NUM                      (IFMAP_CHANNEL_NUM),
        .WEIGHT_WIDTH                           (WEIGHT_WIDTH),
        .WEIGHT_HEIGHT                          (WEIGHT_HEIGHT),
        .IFMAP_WIDTH                            (IFMAP_WIDTH),
        .IFMAP_HEIGHT                           (IFMAP_HEIGHT),
        .OFMAP_WIDTH                            (OFMAP_WIDTH),
        .OFMAP_HEIGHT                           (OFMAP_HEIGHT)
    ) memorycontroller (
        .clk                                    (clk),
        .rstn                                   (rstn),
        .start_in                               (start_in_toggle),
        .ofmap_ready_in                         (ofmap_ready),
        .w_prefetch_out                         (w_prefetch),
        .w_addr_out                             (w_addr),
        .w_read_en_out                          (w_read_en),
        .ifmap_start_out                        (ifmap_start),
        .ifmap_addr_out                         (ifmap_addr),
        .ifmap_read_en_out                      (ifmap_read_en),
        .ofmap_addr_out                         (psum_addr),
        .ofmap_write_en_out                     (ofmap_write_en),
        .ofmap_write_done_out                   (ofmap_write_done),
        .mac_done_out                           (mac_done),
        .i_state_cnt                            (i_state_cnt),
        .i_state_err                            (i_state_err),
        .w_state_cnt                            (w_state_cnt),
        .w_state_err                            (w_state_err),
        .o_state_cnt                            (o_state_cnt),
        .o_state_err                            (o_state_err)
    );

    MacArray #(
        .MAC_ROW                                (MAC_ROW),
        .MAC_COL                                (MAC_COL),
        .IFMAP_BITWIDTH                         (IFMAP_BITWIDTH),
        .W_BITWIDTH                             (W_BITWIDTH),
        .OFMAP_BITWIDTH                         (OFMAP_BITWIDTH)
    ) macarray (
        .clk                                    (clk),   
        .rstn                                   (rstn),
        .w_prefetch_in                          (w_prefetch),
        .w_enable_in                            (w_enable),
        .w_data_in                              (w_data),
        .ifmap_start_in                         (ifmap_start),
        .ifmap_enable_in                        (ifmap_enable),
        .ifmap_data_in                          (ififo_data),
        .ofmap_valid_out                        (ofmap_valid),
        .ofmap_data_out                         (ofmap_data)
    );

    // verificate functionality
    assign test_output_out                      = psum_data;
    assign psum_addr_mux                        = test_check_in ? test_output_addr_in : psum_addr;

    // Memory instances
    SinglePortRam #(
        .RAM_WIDTH                              (IFMAP_BITWIDTH*MAC_ROW),
        .RAM_ADDR_BITS                          (IFMAP_ADDR_BIT),
        .INIT_FILE_NAME                         ("./data/ifmap.hex")
    )
    i_mem
    (   
        .rstn                                   (rstn),
        .clk                                    (clk),
        .we_in                                  (1'b0),
        .addr_in                                (ifmap_addr),
        .wdata_in                               ({(IFMAP_BITWIDTH*MAC_ROW){1'b0}}),
        .rdata_out                              (ifmap_data)
    );

    SinglePortRam #(
        .RAM_WIDTH                              (W_BITWIDTH*MAC_COL),
        .RAM_ADDR_BITS                          (W_ADDR_BIT),
        .INIT_FILE_NAME                         ("./data/weight.hex")
    )
    w_mem
    (
        .rstn                                   (rstn),
        .clk                                    (clk),
        .we_in                                  (1'b0),
        .addr_in                                (w_addr),
        .wdata_in                               ({(W_BITWIDTH*MAC_COL){1'b0}}),
        .rdata_out                              (w_data)
    );

    OutputMemory #(
        .INIT_FILE_NAME                        ("./data/init_ofmap.hex")
    )
    o_mem
    (
        .clock                                  (clk),            
        .rdaddress                              (psum_addr_mux),                
        .rdata_out                              (psum_data),
        .we_in                                  (ofmap_wen),            
        .wraddress                              (ofmap_addr),                
        .wdata_in                               (ofmap_wdata)            
    );

//Added by Mao for Equivalence Checking
    `ifdef SVA
        parameter RAM_WIDTH                     = 32;
        parameter RAM_ADDR_BITS                 = 10;
        logic [RAM_WIDTH-1:0]                   test3[(2**RAM_ADDR_BITS)-1:0];
        logic [RAM_WIDTH-1:0]                   test2[(2**RAM_ADDR_BITS)-1:0];
        logic [RAM_WIDTH-1:0]                   test1[(2**RAM_ADDR_BITS)-1:0];
        logic [RAM_WIDTH-1:0]                   test0[(2**RAM_ADDR_BITS)-1:0];

        property equivalence;
            @(posedge clk) disable iff (~rstn)
                finish_out |-> ((o_mem.ofmap_mem0.mem == test0) && (o_mem.ofmap_mem1.mem == test1) && (o_mem.ofmap_mem2.mem == test2) && (o_mem.ofmap_mem3.mem == test3));
        endproperty

        property test_addr;
            @(posedge clk) disable iff (~rstn)
                test_output_addr_in == 0;
        endproperty

        property test_check;
            @(posedge clk) disable iff (~rstn)
                test_check_in == 0;
        endproperty

        property finish;
            @(posedge clk) disable iff (~rstn)
                finish_out == 1'b1;
        endproperty

        assume property(test_addr);
        assume property(test_check);
        //assume property(start);
        //assume property(initialization_imap);
        //assume property(initialization_wmap);
        //assert property(equivalence);
        cover property(finish);
        assert property(equivalence);
    `endif

    temporal_property_checker #(
        .MAC_ROW                                (MAC_ROW),
        .MAC_COL                                (MAC_COL),
        .OFMAP_CHANNEL_NUM                      (OFMAP_CHANNEL_NUM),
        .IFMAP_CHANNEL_NUM                      (IFMAP_CHANNEL_NUM),
        .WEIGHT_WIDTH                           (WEIGHT_WIDTH),
        .WEIGHT_HEIGHT                          (WEIGHT_HEIGHT),
        .IFMAP_WIDTH                            (IFMAP_WIDTH),
        .IFMAP_HEIGHT                           (IFMAP_HEIGHT),
        .OFMAP_WIDTH                            (OFMAP_WIDTH),
        .OFMAP_HEIGHT                           (OFMAP_HEIGHT)        
    )
    sva
    (
        .clk                                    (clk),
        .rstn                                   (rstn),
        .start_in                               (start_in_toggle),
        .finish_out                             (finish_out),
        .prop_i_state_cnt                       (prop_i_state_cnt),
        .prop_i_state_err                       (prop_i_state_err),
        .prop_w_state_cnt                       (prop_w_state_cnt),
        .prop_w_state_err                       (prop_w_state_err),
        .prop_o_state_cnt                       (prop_o_state_cnt),
        .prop_o_state_err                       (prop_o_state_err)
    );
endmodule

module temporal_property_checker
#(
    parameter MAC_ROW                           = 16,
    parameter MAC_COL                           = 16,

    // operation parameter
    parameter OFMAP_CHANNEL_NUM                 = 64,
    parameter IFMAP_CHANNEL_NUM                 = 32,
    parameter WEIGHT_WIDTH                      = 3,
    parameter WEIGHT_HEIGHT                     = 3,
    parameter IFMAP_WIDTH                       = 16,
    parameter IFMAP_HEIGHT                      = 16,
    parameter OFMAP_WIDTH                       = 14,
    parameter OFMAP_HEIGHT                      = 14
)
(
    input logic                                 clk, 
    input logic                                 rstn, 
    input logic                                 start_in, 
    input logic                                 finish_out,
    input logic [9:0]                           prop_i_state_cnt,
    input logic [9:0]                           prop_i_state_err,
    input logic [9:0]                           prop_w_state_cnt,
    input logic [9:0]                           prop_w_state_err,
    input logic [9:0]                           prop_o_state_cnt,
    input logic [9:0]                           prop_o_state_err
);
    // default clocking c0 @(posedge clk); endclocking
    localparam NUM_FETCH = (WEIGHT_WIDTH * WEIGHT_HEIGHT) * (IFMAP_CHANNEL_NUM / MAC_ROW) * (OFMAP_CHANNEL_NUM / MAC_COL);
    localparam NUM_STORE = (WEIGHT_WIDTH * WEIGHT_HEIGHT) * (IFMAP_CHANNEL_NUM / MAC_ROW);

    property temporal_behavior_001;
        // @(posedge clk) not (~rstn && start_in);
        @(posedge clk) start_in |-> rstn;
        // @(posedge clk) start_in;
    endproperty cover property (temporal_behavior_001);

    property temporal_behavior_002;
        @(posedge clk) start_in |-> ##214 finish_out;               
    endproperty assert property (temporal_behavior_002);

    property temporal_behavior_003;
        @(posedge clk) (finish_out |-> (prop_i_state_cnt == NUM_FETCH));
    endproperty assert property (temporal_behavior_003);

    property temporal_behavior_004;
        @(posedge clk) (finish_out |-> (prop_w_state_cnt == NUM_FETCH));
    endproperty assert property (temporal_behavior_004);

    property temporal_behavior_005;
        @(posedge clk) (finish_out |-> (prop_o_state_cnt == NUM_STORE));
    endproperty assert property (temporal_behavior_005);

    property temporal_behavior_006;
        @(posedge clk) (finish_out |-> (prop_i_state_err == 0));
    endproperty assert property (temporal_behavior_006);

    property temporal_behavior_007;
        @(posedge clk) (finish_out |-> (prop_w_state_err == 0));
    endproperty assert property (temporal_behavior_007);

    property temporal_behavior_008;
        @(posedge clk) (finish_out |-> (prop_o_state_err == 0));
    endproperty assert property (temporal_behavior_008);

endmodule
