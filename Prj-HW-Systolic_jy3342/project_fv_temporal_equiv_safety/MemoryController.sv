`timescale 1 ns / 1 ps

module MemoryController
#(
    // logic parameter
    parameter MAC_ROW                                           = 16,
    parameter MAC_COL                                           = 16,
    parameter W_BITWIDTH                                        = 8,
    parameter IFMAP_BITWIDTH                                    = 16,
    parameter OFMAP_BITWIDTH                                    = 32,
    parameter W_ADDR_BIT                                        = 11,
    parameter IFMAP_ADDR_BIT                                    = 9,
    parameter OFMAP_ADDR_BIT                                    = 10,
    // operation parameter
    parameter OFMAP_CHANNEL_NUM                                 = 64,
    parameter IFMAP_CHANNEL_NUM                                 = 32,
    parameter WEIGHT_WIDTH                                      = 3,
    parameter WEIGHT_HEIGHT                                     = 3,
    parameter IFMAP_WIDTH                                       = 16,
    parameter IFMAP_HEIGHT                                      = 16,
    parameter OFMAP_WIDTH                                       = 14,
    parameter OFMAP_HEIGHT                                      = 14
)
(
    input  logic                                                clk,
    input  logic                                                rstn,

    input  logic                                                start_in,
    
    input  logic                                                ofmap_ready_in,

    output logic                                                w_prefetch_out,
    output logic [W_ADDR_BIT-1:0]                               w_addr_out,
    output logic                                                w_read_en_out,

    output logic                                                ifmap_start_out,
    output logic [IFMAP_ADDR_BIT-1:0]                           ifmap_addr_out,
    output logic                                                ifmap_read_en_out,

    output logic [OFMAP_ADDR_BIT-1:0]                           ofmap_addr_out,
    output logic                                                ofmap_write_en_out,
    output logic                                                ofmap_write_done_out,

    output logic                                                mac_done_out,
    output logic [9:0]                                          i_state_cnt,
    output logic [9:0]                                          i_state_err,
    output logic [9:0]                                          w_state_cnt,
    output logic [9:0]                                          w_state_err,
    output logic [9:0]                                          o_state_cnt,
    output logic [9:0]                                          o_state_err

);
    localparam W_CNT2                                           = OFMAP_CHANNEL_NUM / MAC_COL;
    localparam W_CNT3                                           = (WEIGHT_WIDTH * WEIGHT_HEIGHT) * (IFMAP_CHANNEL_NUM / MAC_ROW);
    localparam IF_CNT4                                          = IFMAP_CHANNEL_NUM / MAC_ROW;
    localparam OF_CNT1                                          = OFMAP_WIDTH * OFMAP_HEIGHT; 

    logic [9:0]                                                 i_state_cnt_ff, i_state_cnt_nxt;
    logic [9:0]                                                 w_state_cnt_ff, w_state_cnt_nxt;
    logic [9:0]                                                 o_state_cnt_ff, o_state_cnt_nxt;
    logic [9:0]                                                 i_state_taken_ff, i_state_taken_nxt;
    logic [9:0]                                                 i_state_err_ff, i_state_err_nxt;
    logic [9:0]                                                 w_state_taken_ff, w_state_taken_nxt;
    logic [9:0]                                                 w_state_err_ff, w_state_err_nxt;
    logic [9:0]                                                 o_state_taken_ff, o_state_taken_nxt;
    logic [9:0]                                                 o_state_err_ff, o_state_err_nxt;

    assign i_state_cnt                                          = i_state_cnt_ff;
    assign i_state_err                                          = i_state_err_ff;
    assign w_state_cnt                                          = w_state_cnt_ff;
    assign w_state_err                                          = w_state_err_ff;
    assign o_state_cnt                                          = o_state_cnt_ff;
    assign o_state_err                                          = o_state_err_ff;

    enum logic [2:0]{
        IDLE,           // 000
        W_START,        // 001
        W_WAIT,         // 010
        W_PREF,         // 011
        IF_START,       // 100
        IF_FEED         // 101
    } state_ff, state_nxt;

    enum logic {
        OF_START,
        OF_WRITE
    } of_state_ff, of_state_nxt;

    struct packed {
        logic [W_ADDR_BIT-1:0]                                  w_addr_ref1;
        logic [W_ADDR_BIT-1:0]                                  w_addr_ref2;
        logic [W_ADDR_BIT-1:0]                                  w_addr_ref3;
        logic [$clog2(MAC_ROW)-1:0]                             w_cnt1;
        logic [$clog2(W_CNT2)-1:0]                              w_cnt2;
        logic [$clog2(W_CNT3)-1:0]                              w_cnt3;

        logic [IFMAP_ADDR_BIT-1:0]                              if_addr_ref1;
        logic [IFMAP_ADDR_BIT-1:0]                              if_addr_ref2;
        logic [IFMAP_ADDR_BIT-1:0]                              if_addr_ref3;
        logic [IFMAP_ADDR_BIT-1:0]                              if_addr_ref4;
        logic [IFMAP_ADDR_BIT-1:0]                              if_addr_ref5;
        logic [$clog2(OFMAP_WIDTH)-1:0]                         if_cnt1;
        logic [$clog2(OFMAP_HEIGHT)-1:0]                        if_cnt2;
        logic [$clog2(W_CNT2)-1:0]                              if_cnt3;
        logic [$clog2(IF_CNT4)-1:0]                             if_cnt4;
        logic [$clog2(WEIGHT_WIDTH)-1:0]                        if_cnt5;
        logic [$clog2(WEIGHT_HEIGHT)-1:0]                       if_cnt6;
    } reg_ff, reg_nxt;

    struct packed {
        logic [OFMAP_ADDR_BIT-1:0]                              of_addr_ref1;
        logic [OFMAP_ADDR_BIT-1:0]                              of_addr_ref2;
        logic [$clog2(OF_CNT1)-1:0]                             of_cnt1;
        logic [$clog2(W_CNT2)-1:0]                              of_cnt2;
        logic [$clog2(W_CNT3)-1:0]                              of_cnt3;
    } of_reg_ff, of_reg_nxt;

    always_ff @(posedge clk) begin
        if (~rstn) begin
            i_state_cnt_ff                                      <= '0;
            w_state_cnt_ff                                      <= '0;
            o_state_cnt_ff                                      <= '0;
            i_state_taken_ff                                    <= '0;
            w_state_taken_ff                                    <= '0;
            o_state_taken_ff                                    <= '0;
            i_state_err_ff                                      <= '0;
            w_state_err_ff                                      <= '0;
            o_state_err_ff                                      <= '0;
        end
        else begin
            i_state_cnt_ff                                      <= i_state_cnt_nxt;
            w_state_cnt_ff                                      <= w_state_cnt_nxt;
            o_state_cnt_ff                                      <= o_state_cnt_nxt;
            i_state_taken_ff                                    <= i_state_taken_nxt;
            w_state_taken_ff                                    <= w_state_taken_nxt;
            o_state_taken_ff                                    <= o_state_taken_nxt;
            i_state_err_ff                                      <= i_state_err_nxt;
            w_state_err_ff                                      <= w_state_err_nxt;
            o_state_err_ff                                      <= o_state_err_nxt;
        end
    end

    always_ff @(posedge clk) begin
        if (~rstn) begin
            state_ff                                            <= IDLE;
            reg_ff                                              <= '0;
        end
        else begin
            state_ff                                            <= state_nxt;
            reg_ff                                              <= reg_nxt;
        end
    end

    always_ff @(posedge clk) begin
        if (~rstn) begin
            of_state_ff                                         <= OF_START;
            of_reg_ff                                           <= '0;
        end
        else begin
            of_state_ff                                         <= of_state_nxt;
            of_reg_ff                                           <= of_reg_nxt;
        end
    end

    always_comb begin
        state_nxt                                               = state_ff;
        reg_nxt                                                 = reg_ff;
        w_prefetch_out                                          = '0;
        w_read_en_out                                           = '0;
        w_addr_out                                              = '0;
        ifmap_start_out                                         = '0;
        ifmap_read_en_out                                       = '0;
        ifmap_addr_out                                          = '0;
        mac_done_out                                            = '0;

        i_state_cnt_nxt                                         = i_state_cnt_ff;
        w_state_cnt_nxt                                         = w_state_cnt_ff;
        i_state_taken_nxt                                       = i_state_taken_ff;
        w_state_taken_nxt                                       = w_state_taken_ff;
        i_state_err_nxt                                         = i_state_err_ff;
        w_state_err_nxt                                         = w_state_err_ff;

        case (state_ff)
            IDLE: begin
                if (start_in) begin
                    state_nxt                                   = W_START;
                    reg_nxt                                     = '0;
                end
            end

            W_START : begin
                state_nxt                                       = W_PREF;
                w_state_cnt_nxt                                 = w_state_cnt_ff + 1;
                
                w_read_en_out                                   = 'b1;
                w_addr_out                                      = reg_ff.w_addr_ref1 + reg_ff.w_addr_ref2 + reg_ff.w_addr_ref3;
                reg_nxt.w_cnt1                                  = reg_ff.w_cnt1 + 'd1;
                reg_nxt.w_addr_ref1                             = reg_ff.w_addr_ref1 + 'd4;
                w_prefetch_out                                  = 'b1;
            end

            W_WAIT : begin
                if (~ofmap_ready_in) begin             
                    if (i_state_taken_ff == OFMAP_WIDTH * OFMAP_HEIGHT-1) begin
                        i_state_err_nxt                         = i_state_err_ff + 0;
                    end
                    else begin
                        i_state_err_nxt                         = i_state_err_ff + 1;
                    end
                    i_state_taken_nxt                           = 0;
                    w_state_cnt_nxt                             = w_state_cnt_ff + 1;
                    state_nxt                                   = W_PREF;
                    
                    w_read_en_out                               = 'b1;
                    w_addr_out                                  = reg_ff.w_addr_ref1 + reg_ff.w_addr_ref2 + reg_ff.w_addr_ref3;
                    reg_nxt.w_cnt1                              = reg_ff.w_cnt1 + 'd1;
                    reg_nxt.w_addr_ref1                         = reg_ff.w_addr_ref1 + 'd4;
                    w_prefetch_out                              = 'b1;
                end
            end

            W_PREF: begin
                w_state_taken_nxt                               = w_state_taken_ff + 1;
                w_read_en_out                                   = 'b1;
                w_addr_out                                      = reg_ff.w_addr_ref1 + reg_ff.w_addr_ref2 + reg_ff.w_addr_ref3;
                if (reg_ff.w_cnt1 == MAC_ROW-1) begin
                    state_nxt                                   = IF_START;
                    reg_nxt.w_cnt1                              = '0;
                    reg_nxt.w_addr_ref1                         = '0;
                    if (reg_ff.w_cnt2 == W_CNT2-1) begin
                        reg_nxt.w_cnt2                          = '0;
                        reg_nxt.w_addr_ref2                     = '0;
                        if (reg_ff.w_cnt3 == W_CNT3-1) begin
                            reg_nxt.w_cnt3                      = '0;
                            reg_nxt.w_addr_ref3                 = '0;
                        end
                        else begin
                            reg_nxt.w_cnt3                      = reg_ff.w_cnt3 + 'd1;
                            reg_nxt.w_addr_ref3                 = reg_ff.w_addr_ref3 + 'd64;
                        end
                    end
                    else begin
                        reg_nxt.w_cnt2                          = reg_ff.w_cnt2 + 'd1;
                        reg_nxt.w_addr_ref2                     = reg_ff.w_addr_ref2 + 'd1;
                    end
                end
                else begin
                    reg_nxt.w_cnt1                              = reg_ff.w_cnt1 + 'd1;
                    reg_nxt.w_addr_ref1                         = reg_ff.w_addr_ref1 + 'd4;
                end
            end

            IF_START : begin
                if (w_state_taken_ff == MAC_COL-1) begin
                    w_state_err_nxt                             = w_state_err_ff + 0;
                end
                else begin
                    w_state_err_nxt                             = w_state_err_ff + 1;
                end
                w_state_taken_nxt                               = 0;
                i_state_cnt_nxt                                 = i_state_cnt_ff + 1;
                state_nxt                                       = IF_FEED;

                ifmap_read_en_out                               = 'b1;
                ifmap_addr_out                                  = reg_ff.if_addr_ref1 + reg_ff.if_addr_ref2 + reg_ff.if_addr_ref3 + reg_ff.if_addr_ref4 + reg_ff.if_addr_ref5;
                reg_nxt.if_cnt1                                 = reg_ff.if_cnt1 + 'd1;
                reg_nxt.if_addr_ref1                            = reg_ff.if_addr_ref1 + 'd2;
                ifmap_start_out                                 = 'b1;
            end

            IF_FEED: begin
                i_state_taken_nxt                               = i_state_taken_ff + 1;
                ifmap_read_en_out                               = 'b1;
                ifmap_addr_out                                  = reg_ff.if_addr_ref1 + reg_ff.if_addr_ref2 + reg_ff.if_addr_ref3 + reg_ff.if_addr_ref4 + reg_ff.if_addr_ref5;
                if (reg_ff.if_cnt1 == OFMAP_WIDTH-1) begin
                    reg_nxt.if_cnt1                             = '0;
                    reg_nxt.if_addr_ref1                        = '0;
                    if (reg_ff.if_cnt2 == OFMAP_HEIGHT-1) begin
                        state_nxt                               = W_WAIT;
                        reg_nxt.if_cnt2                         = '0;
                        reg_nxt.if_addr_ref2                    = '0;
                        if (reg_ff.if_cnt3 == W_CNT2-1) begin
                            reg_nxt.if_cnt3                     = '0;
                            if (reg_ff.if_cnt4 == IF_CNT4-1) begin
                                reg_nxt.if_cnt4                 = '0;
                                reg_nxt.if_addr_ref3            = '0;
                                if (reg_ff.if_cnt5 == WEIGHT_WIDTH-1) begin
                                    reg_nxt.if_cnt5             = '0;
                                    reg_nxt.if_addr_ref4        = '0;
                                    if (reg_ff.if_cnt6 == WEIGHT_HEIGHT-1) begin
                                        state_nxt               = IDLE;
                                        mac_done_out            = 'b1;
                                        reg_nxt.if_cnt6         = '0;
                                        reg_nxt.if_addr_ref5    = '0;
                                    end
                                    else begin
                                        reg_nxt.if_cnt6         = reg_ff.if_cnt6 + 'd1;
                                        reg_nxt.if_addr_ref5    = reg_ff.if_addr_ref5 + 'd32;
                                    end
                                end
                                else begin
                                    reg_nxt.if_cnt5             = reg_ff.if_cnt5 + 'd1;
                                    reg_nxt.if_addr_ref4        = reg_ff.if_addr_ref4 + 'd2;
                                end
                            end
                            else begin
                                reg_nxt.if_cnt4                 = reg_ff.if_cnt4 + 'd1;
                                reg_nxt.if_addr_ref3            = reg_ff.if_addr_ref3 + 'd1;
                            end
                        end
                        else begin
                            reg_nxt.if_cnt3                     = reg_ff.if_cnt3 + 'd1;
                        end
                    end
                    else begin
                        reg_nxt.if_cnt2                         = reg_ff.if_cnt2 + 'd1;
                        reg_nxt.if_addr_ref2                    = reg_ff.if_addr_ref2 + 'd32;
                    end
                end
                else begin
                    reg_nxt.if_cnt1                             = reg_ff.if_cnt1 + 'd1;
                    reg_nxt.if_addr_ref1                        = reg_ff.if_addr_ref1 + 'd2;
                end
            end
        endcase
    end
    
    always_comb begin
        of_state_nxt                                            = of_state_ff;
        of_reg_nxt                                              = of_reg_ff;
        ofmap_write_en_out                                      = '0;
        ofmap_write_done_out                                    = '0;
        ofmap_addr_out                                          = '0;

        o_state_cnt_nxt                                         = o_state_cnt_ff;
        o_state_taken_nxt                                       = o_state_taken_ff;
        o_state_err_nxt                                         = o_state_err_ff;

        case (of_state_ff)
            OF_START: begin
                if (ofmap_ready_in) begin
                    of_state_nxt                                = OF_WRITE;
                                        o_state_cnt_nxt                             = o_state_cnt_ff + 1;
                    o_state_taken_nxt                           = 0;
                    if (o_state_taken_ff == OFMAP_WIDTH * OFMAP_HEIGHT * OFMAP_CHANNEL_NUM / MAC_COL-1) begin
                        o_state_err_nxt                         = o_state_err_ff + 0;
                    end
                    else begin
                        o_state_err_nxt                         = o_state_err_ff + 1;
                    end

                    ofmap_write_en_out                          = 'b1;
                    ofmap_addr_out                              = of_reg_ff.of_addr_ref1 + of_reg_ff.of_addr_ref2;
                    of_reg_nxt.of_cnt1                          = of_reg_ff.of_cnt1 + 'd1;
                    of_reg_nxt.of_addr_ref1                     = of_reg_ff.of_addr_ref1 + 'd4;
                end
            end
            OF_WRITE: begin
                if (ofmap_ready_in) begin    
                    o_state_taken_nxt                           = o_state_taken_ff + 1;
                    ofmap_write_en_out                          = 'b1;
                    ofmap_addr_out                              = of_reg_ff.of_addr_ref1 + of_reg_ff.of_addr_ref2;
                    if (of_reg_ff.of_cnt1 == OF_CNT1-1) begin
                        of_reg_nxt.of_cnt1                      = '0;
                        of_reg_nxt.of_addr_ref1                 = '0;
                        if (of_reg_ff.of_cnt2 == W_CNT2-1) begin
                            of_state_nxt                        = OF_START;
                            of_reg_nxt.of_cnt2                  = '0;
                            of_reg_nxt.of_addr_ref2             = '0;
                            of_reg_nxt.of_cnt3                  = of_reg_ff.of_cnt3 + 'd1;
                            if (of_reg_ff.of_cnt3 == W_CNT3-1) begin
                                ofmap_write_done_out            = 'b1;
                            end
                        end
                        else begin
                            of_reg_nxt.of_cnt2                  = of_reg_ff.of_cnt2 + 'd1;
                            of_reg_nxt.of_addr_ref2             = of_reg_ff.of_addr_ref2 + 'd1;
                        end
                    end
                    else begin
                        of_reg_nxt.of_cnt1                      = of_reg_ff.of_cnt1 + 'd1;
                        of_reg_nxt.of_addr_ref1                 = of_reg_ff.of_addr_ref1 + 'd4;
                    end
                end
            end
        endcase
    end

endmodule
