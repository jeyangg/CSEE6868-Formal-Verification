`timescale 1 ns / 1 ps

module Mac
#(
    parameter IFMAP_BITWIDTH                                            = 16,
    parameter W_BITWIDTH                                                = 8,
    parameter OFMAP_BITWIDTH                                            = 32
)
(
    input  logic                                                        clk,
    input  logic                                                        rstn,

    input  logic                                                        w_enable_in,
    input  logic [W_BITWIDTH-1:0]                                       w_data_in,
    input  logic                                                        ifmap_enable_in,
    input  logic [IFMAP_BITWIDTH-1:0]                                   ifmap_data_in,
    input  logic [OFMAP_BITWIDTH-1:0]                                   psum_data_in,

    output logic [W_BITWIDTH-1:0]                                       w_data_out,
    output logic                                                        ifmap_enable_out,
    output logic [IFMAP_BITWIDTH-1:0]                                   ifmap_data_out,
    output logic [OFMAP_BITWIDTH-1:0]                                   psum_data_out
);

    logic signed [W_BITWIDTH-1:0]                                       w_data_ff;
	logic signed [W_BITWIDTH-1:0]                                       w_data_nxt;
    logic signed [IFMAP_BITWIDTH-1:0]                                   ifmap_data_ff;
	logic signed [IFMAP_BITWIDTH-1:0]                                   ifmap_data_nxt;
    logic signed [OFMAP_BITWIDTH-1:0]                                   psum_in;
    logic signed [OFMAP_BITWIDTH-1:0]                                   pmul_data;
    logic signed [OFMAP_BITWIDTH-1:0]                                   psum_data;
    reg signed  [OFMAP_BITWIDTH*2-1:0]					                mul_res;
    reg signed  [OFMAP_BITWIDTH*2-1:0]					                mul_sum_res;

	assign w_data_out                                                   = w_data_ff;
	assign ifmap_data_out                                               = ifmap_data_ff;
	 
    always_ff @(posedge clk) begin
        if(~rstn) begin
            ifmap_enable_out                                            <= 0;
        end
        else begin
            w_data_ff                                                   <= w_data_nxt;
            ifmap_enable_out                                            <= ifmap_enable_in;
            ifmap_data_ff                                               <= ifmap_data_nxt;
            psum_data_out                                               <= psum_data;
        end
    end

    always_comb begin
        w_data_nxt                                                      = w_enable_in ? w_data_in : w_data_ff;
        ifmap_data_nxt                                                  = ifmap_enable_in ? ifmap_data_in : ifmap_data_ff;
        psum_in                                                         = psum_data_in;
        pmul_data                                                       = w_data_ff * ifmap_data_nxt;
        psum_data                                                       = pmul_data + psum_in;
	mul_res								                                = w_data_ff * ifmap_data_nxt;
	mul_sum_res							                                = pmul_data + psum_in;
    end

    //------------------------------- Overflow Checking ----------------------------------------------
    property mulSmallerThanMax;
	@(posedge clk) (mul_res <= $signed(64'h7FFFFFFF));
    endproperty
    property mulLargerThanMin;
	@(posedge clk) (mul_res >= $signed(-64'h80000000));
    endproperty
    property sumSmallerThanMax;
	@(posedge clk) (mul_sum_res <= $signed(64'h7FFFFFFF));
    endproperty
    property sumLargerThanMin;
	@(posedge clk) (mul_sum_res >= $signed(-64'h80000000));
    endproperty

    assert property(mulSmallerThanMax);
    assert property(mulLargerThanMin);
    assert property(sumSmallerThanMax);
    assert property(sumLargerThanMin);
    //------------------------------- END Overflow Checking ------------------------------------------
    //------------------------------- Overlap Checking -----------------------------------------------
    property no_data_overlapping;
      @(posedge clk) not (w_enable_in && ifmap_enable_in);
    endproperty 

    assert property (no_data_overlapping);
    //------------------------------- END Overlap Checking -------------------------------------------
    //------------------------------- Data in Seq Checking -------------------------------------------
    sequence weight_in;
        w_enable_in ##15 !w_enable_in;
    endsequence
    sequence weight_in_delay;
        ##[0:15] !w_enable_in;
    endsequence
    sequence ifmap_in_delay;
        ##[16:32] ifmap_enable_in;
    endsequence

    property leading_weight_data_in;
        @(posedge clk) weight_in |-> ifmap_in_delay;
    endproperty
    property ifmap_in_seq;
	@(posedge clk) $fell(ifmap_enable_in) |-> weight_in_delay;
    endproperty

    assert property (leading_weight_data_in);
    assert property (ifmap_in_seq);
    //------------------------------- END Data in Seq Checking ---------------------------------------
endmodule
