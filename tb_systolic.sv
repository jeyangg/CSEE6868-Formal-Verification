/////////////////////////////////////////////////////////////////////
//
// EE878(B) Project 3
// Title: tb_Systolic.sv
//
/////////////////////////////////////////////////////////////////////
 
`timescale 1ns / 1ps

module tb_systolic; 

    // logic parameter
    localparam MAC_ROW                          = 16;
    localparam MAC_COL                          = 16;
    localparam W_BITWIDTH                       = 8;
    localparam IFMAP_BITWIDTH                   = 16;
    localparam OFMAP_BITWIDTH                   = 32;
    localparam W_ADDR_BIT                       = 11;
    localparam IFMAP_ADDR_BIT                   = 9;
    localparam OFMAP_ADDR_BIT                   = 10;
    // operation parameter
    localparam OFMAP_CHANNEL_NUM                = 64;
    localparam IFMAP_CHANNEL_NUM                = 32;
    localparam WEIGHT_WIDTH                     = 3;
    localparam WEIGHT_HEIGHT                    = 3;
    localparam IFMAP_WIDTH                      = 16;
    localparam IFMAP_HEIGHT                     = 16;
    localparam OFMAP_WIDTH                      = 14;
    localparam OFMAP_HEIGHT                     = 14;
    localparam OFMAP_NUM                        = 784;
    // initialization data path
    localparam IFMAP_DATA_PATH                  = "./data/ifmap.hex";
    localparam WEIGHT_DATA_PATH                 = "./data/weight.hex";
    localparam INIT_OFMAP_DATA_PATH             = "./data/init_ofmap.hex";
    localparam OFMAP_DATA_PATH                  = "./data/ofmap.hex";

    int                                         error;

    logic                                       clk;
    logic                                       rstn;

    logic                                       start_in;

    logic                                       finish_out;

    logic [OFMAP_ADDR_BIT-1:0]                  test_output_addr_in;
    logic [OFMAP_ADDR_BIT-1:0]                  ref_num;
    logic                                       test_check_in;
    logic                                       comparing;
    logic [MAC_COL*OFMAP_BITWIDTH-1:0]          test_output_out;
    logic [MAC_COL*OFMAP_BITWIDTH-1:0]          output_result[OFMAP_NUM-1:0];
    logic [MAC_COL*OFMAP_BITWIDTH-1:0]          ref_output;
    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     test_output_out_tmp;
    logic [MAC_COL-1:0][OFMAP_BITWIDTH-1:0]     ref_output_tmp;

/////////////////////////////////////////////////////////////////////
// Test

    // vcs dump
    initial $vcdplusfile("vcdplus_rtl.vpd");
    // initial $vcdpluson();
    // initial $vcdplusmemon();

    initial begin
        clk                                     = 1'b0;
        fork
            forever #5 clk        = ~clk;
        join
    end

    initial begin
        error                                   = 0;
        test_output_addr_in                     = '0;
        test_check_in                           = '0;
    end

    initial begin
        #1000000;
        $finish;
    end

    initial begin
        $readmemh(OFMAP_DATA_PATH, output_result);
    end

    initial begin
        rstn                                    = 1'b0;
        start_in                                = 1'b0;
        repeat(10) @(posedge clk);
        rstn                                    = 1'b1;

        repeat(2) @(posedge clk);

        start_in                                = 1'b1;
        @(posedge clk);
        start_in                                = 1'b0;

        wait(finish_out)

        repeat(10)@(posedge clk);

        test_check_in                           = 1'b1;
        while (test_output_addr_in != OFMAP_NUM - 1) begin
            @(posedge clk);
            test_output_addr_in                 = test_output_addr_in + 'd1;
        end

        @(posedge clk);

        if (error == 0) $display("Successfully Completed");
        else begin
           $display("Simulation Failed"); 
           $display("Error: %d", error+1); 
        end
        $finish;
    end

    genvar i;

    generate
        for (i = 0; i < MAC_COL; i++) begin
            assign test_output_out_tmp[i]       = test_output_out[OFMAP_BITWIDTH*(i+1)-1:OFMAP_BITWIDTH*i];
            assign ref_output_tmp[i]            = ref_output[OFMAP_BITWIDTH*(i+1)-1:OFMAP_BITWIDTH*i];
        end
    endgenerate

    assign ref_output                           = output_result[ref_num];

    always @(posedge clk) begin
        if (comparing) begin
            if (ref_output != test_output_out) error++;
        end
    end

    always @(posedge clk) begin
        ref_num                                 <= #11 test_output_addr_in;
        comparing                               <= #11 test_check_in;
    end

/////////////////////////////////////////////////////////////////////
// ********** User Logic **********

    Systolic 
    #(
        .MAC_ROW                                (MAC_ROW             ),
        .MAC_COL                                (MAC_COL             ),
        .W_BITWIDTH                             (W_BITWIDTH          ),
        .IFMAP_BITWIDTH                         (IFMAP_BITWIDTH      ),
        .OFMAP_BITWIDTH                         (OFMAP_BITWIDTH      ),
        .W_ADDR_BIT                             (W_ADDR_BIT          ),
        .IFMAP_ADDR_BIT                         (IFMAP_ADDR_BIT      ),
        .OFMAP_ADDR_BIT                         (OFMAP_ADDR_BIT      ),
        .OFMAP_CHANNEL_NUM                      (OFMAP_CHANNEL_NUM   ),
        .IFMAP_CHANNEL_NUM                      (IFMAP_CHANNEL_NUM   ),
        .WEIGHT_WIDTH                           (WEIGHT_WIDTH        ),
        .WEIGHT_HEIGHT                          (WEIGHT_HEIGHT       ),
        .IFMAP_WIDTH                            (IFMAP_WIDTH         ),
        .IFMAP_HEIGHT                           (IFMAP_HEIGHT        ),
        .OFMAP_WIDTH                            (OFMAP_WIDTH         ),
        .OFMAP_HEIGHT                           (OFMAP_HEIGHT        ),
        .IFMAP_DATA_PATH                        (IFMAP_DATA_PATH     ),
        .WEIGHT_DATA_PATH                       (WEIGHT_DATA_PATH    ),
        .OFMAP_DATA_PATH                        (INIT_OFMAP_DATA_PATH)
    )
    dut
    (
        .clk                                    (clk),
        .rstn                                   (rstn),
        .start_in                               (start_in),
        .finish_out                             (finish_out),
        .test_output_addr_in                    (test_output_addr_in),
        .test_check_in                          (test_check_in),
        .test_output_out                        (test_output_out)
    );

endmodule