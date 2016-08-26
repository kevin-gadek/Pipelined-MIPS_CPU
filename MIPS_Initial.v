//-----------------------------------------------------------------
// Module Name   : clk_gen
// Description   : Generate 4 second and 5KHz clock cycle from
//                 the 50MHz clock on the Nexsys2 board
//------------------------------------------------------------------
module clk_gen(
	input			clk50MHz, reset, 
	output reg		clksec );

	reg 			clk_5KHz;
	integer 		count, count1;
	
	always@(posedge clk50MHz) begin
		if(reset) begin
			count = 0;
			count1 = 0;
			clksec = 0;
			clk_5KHz =0;
		end else begin
			if (count == 50000000) begin
				// Just toggle after certain number of seconds
				clksec = ~clksec;
				count = 0;
			end
			if (count1 == 20000) begin
				clk_5KHz = ~clk_5KHz;
				count1 = 0;
			end
			count = count + 1;
			count1 = count1 + 1;
		end
	end
endmodule

//------------------------------------------------
// Source Code for a Single-cycle MIPS Processor (supports partial instruction)
// Developed by D. Hung, D. Herda and G. Gerken,
// based on the following source code provided by
// David_Harris@hmc.edu (9 November 2005):
//    mipstop.v
//    mipsmem.v
//    mips.v
//    mipsparts.v
//------------------------------------------------

// Main Decoder
module maindec(
	input	[ 5:0]	op,
	output			memtoreg, memwrite, branch, alusrc, regdst, regwrite, jump, jal, //jr, multwrite, mflo, mfhi,
	output	[ 1:0]	aluop );

	reg 	[ 9:0]	controls;

	assign {regwrite, regdst, alusrc, branch, memwrite, memtoreg, jump, aluop, jal} = controls;

	always @(*)
		case(op)
			6'b000000: controls <= 10'b1100000100; //Rtype
			6'b100011: controls <= 10'b1010010000; //LW
			6'b101011: controls <= 10'b0010100000; //SW
			6'b000100: controls <= 10'b0001000010; //BEQ
			6'b001000: controls <= 10'b1010000000; //ADDI
			6'b000010: controls <= 10'b0000001000; //J
			6'b000011: controls <= 10'b1000001001; //JAL
			default:   controls <= 14'bxxxxxxxxx; //???
		endcase
endmodule

// ALU Decoder
module aludec(
	input		[5:0]	funct,
	input		[1:0]	aluop,
	output reg	[2:0]	alucontrol,
	output reg          jr, multwrite, mflo, mfhi);

always @(*)
    case(aluop) //4. Added jr and "mult" functionality.
      2'b00: begin
				alucontrol <= 3'b010;  // add
				jr <= 1'b0;
				multwrite <= 1'b0;
				mfhi <= 1'b0;
				mflo <= 1'b0;
			 end
      2'b01: begin
				alucontrol <= 3'b110;  // sub
				jr <= 1'b0;
				multwrite <= 1'b0;
				mfhi <= 1'b0;
				mflo <= 1'b0;
			 end
      default: case(funct)          // RTYPE
          6'b100000:begin //ADD
						alucontrol <= 3'b010; // ADD
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					 end
          6'b100010:begin //SUB
						alucontrol <= 3'b110; // SUB
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					 end
          6'b100100:begin //AND
						alucontrol <= 3'b000; // AND
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					 end
          6'b100101:begin //OR
						alucontrol <= 3'b001; // OR
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					end
          6'b101010:begin //SLT
						alucontrol <= 3'b111; // SLT
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					end
		  6'b001000:begin //2. JR funct = 0x08 = 00_1000
						alucontrol <= 3'b010; // JR
						jr <= 1'b1; 
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					end	
		  6'b011000:begin //2. MULT funct = 0x18 = 01_1000
						alucontrol <= 3'b010; // MULT
						jr <= 1'b0; //2. JR funct = 0x08 = 0x00001000
						multwrite <= 1'b1;
						mfhi <= 1'b0;
						mflo <= 1'b0;
					end					
		  6'b010000:begin //2. MFHI funct = 0x10 = 01_0000
						alucontrol <= 3'b010;
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b1;
						mflo <= 1'b0;
					end					
		  6'b010010:begin //2. MFLO funct = 0x12 = 01_0010
						alucontrol <= 3'b010;
						jr <= 1'b0;
						multwrite <= 1'b0;
						mfhi <= 1'b0;
						mflo <= 1'b1;
					end			
          default:   begin //3. Added jr and "mult" signals to default case.
						alucontrol <= 3'bxxx; // ???
						jr <= 1'bx; //?
						multwrite <= 1'bx; //?
						mfhi <= 1'bx; //?
						mflo <= 1'bx; //?
					 end
        endcase
    endcase
endmodule
// ALU
module alu(
	input		[31:0]	a, b, 
	input		[ 2:0]	alucont, 
	output reg	[31:0]	result);
	//output			zero ); ****Deleted - dont need signal in pipeline

	wire	[31:0]	b2, sum, slt;

	assign b2 = alucont[2] ? ~b:b; 
	assign sum = a + b2 + alucont[2];
	assign slt = sum[31];

	always@(*)
		case(alucont[1:0])
			2'b00: result <= a & b;
			2'b01: result <= a | b;
			2'b10: result <= sum;
			2'b11: result <= slt;
		endcase

	//assign zero = (result == 32'b0);
endmodule

// Adder
module adder(
	input	[31:0]	a, b,
	output	[31:0]	y );

	assign y = a + b;
endmodule

// Two-bit left shifter
module sl2(
	input	[31:0]	a,
	output	[31:0]	y );

	// shift left by 2
	assign y = {a[29:0], 2'b00};
endmodule

// Sign Extension Unit
module signext(
	input	[15:0]	a,
	output	[31:0]	y );

	assign y = {{16{a[15]}}, a};
endmodule

// Parameterized Register
module flopr #(parameter WIDTH = 8) (
	input					clk, reset,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q);

	always @(posedge clk, posedge reset)
		if (reset) q <= 0;
		else       q <= d;
endmodule

module multiplier (input [31:0] a, [31:0]b,
					output [31:0] p_hi, output [31:0] p_lo);
	reg [64:0] result;
	
	always @(*)
		result = a * b;
	assign p_hi = result[63:32];
	assign p_lo = result[31:0];
endmodule

module flopenr #(parameter WIDTH = 8) (
	input					clk, reset,
	input					en,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q);

	always @(posedge clk, posedge reset)
		if      (reset) q <= 0;
		else if (en)    q <= d;
endmodule

module flopenr2 #(parameter WIDTH = 8) (
	input					clk, reset,
	input					en,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q,
	input		[WIDTH-1:0]	d2, 
	output reg	[WIDTH-1:0]	q2);

	always @(posedge clk, posedge reset)
		if      (reset) q <= 0;
		else if (en)   
			begin	
				q <= d;
				q2 <= d2;
			end
endmodule

module flopr10 #(parameter WIDTH = 8) (
	input					clk, reset,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q,
	input		[WIDTH-1:0]	d2, 
	output reg	[WIDTH-1:0]	q2,
	input		[4:0]	    d3, 
	output reg	[4:0]	    q3,
	input		[4:0]	    d4, 
	output reg	[4:0]	    q4,
	input		[4:0]	    d5, 
	output reg	[4:0]	    q5,
	input		[WIDTH-1:0]	d6, 
	output reg	[WIDTH-1:0]	q6,
	input 		[WIDTH-1:0] d7,
	output reg  [WIDTH-1:0] q7,
	input 		[WIDTH-1:0] d8,
	output reg  [WIDTH-1:0] q8,
	input 		[WIDTH-1:0] d9,
	output reg  [WIDTH-1:0] q9,
	input 		[WIDTH-1:0] d10,
	output reg  [WIDTH-1:0] q10);

	always@(posedge clk, posedge reset) begin
		if      (reset) q <= 0;
		else   
			begin	
				q <= d;
				q2 <= d2;
				q3 <= d3;
				q4 <= d4;
				q5 <= d5;
				q6 <= d6;			
				q7 <= d7;
				q8 <= q8;
				q9 <= q9;
				q10<= d10;
			end
    end
endmodule

module flopr11 #(parameter WIDTH = 8) (
	input					clk, reset,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q,
	input		[WIDTH-1:0]	d2,
	output reg	[WIDTH-1:0]	q2,
	input		[4:0]	    d3, 
	output reg	[4:0]	    q3,
	input		[4:0]	    d4, 
	output reg	[4:0]	    q4,
	input		[4:0]	    d5, 
	output reg	[4:0]	    q5,
	input		[WIDTH-1:0]	d6, 
	output reg	[WIDTH-1:0]	q6,
	input 		[WIDTH-1:0] d7,
	output reg  [WIDTH-1:0] q7,
	input 		[WIDTH-1:0] d8,
	output reg  [WIDTH-1:0] q8,
	input 		[WIDTH-1:0] d9,
	output reg  [WIDTH-1:0] q9,
	input 		[WIDTH-1:0] d10,
	output reg  [WIDTH-1:0] q10,
	input 		[WIDTH-1:0] d11,
	output reg  [WIDTH-1:0] q11);

	always @(posedge clk, posedge reset) begin
		if      (reset) q <= 0;
		else   
			begin	
				q <= d;
				q2 <= d2;
				q3 <= d3;
				q4 <= d4;
				q5 <= d5;
				q6 <= d6;			
				q7 <= d7;
				q8 <= q8;
				q9 <= q9;
				q10<= d10;
				q11<= d11;
			end
    end
endmodule

module flopr15 #(parameter WIDTH = 8) (
	input					clk, reset,
	input		[WIDTH-1:0]	d, 
	output reg	[WIDTH-1:0]	q,
	input		[WIDTH-1:0]	d2, 
	output reg	[WIDTH-1:0]	q2,
	input		[4:0]	    d3, 
	output reg	[4:0]	    q3,
	input		[4:0]	    d4, 
	output reg	[4:0]	    q4,
	input		[4:0]	    d5, 
	output reg	[4:0]	    q5,
	input		[WIDTH-1:0]	d6, 
	output reg	[WIDTH-1:0]	q6,
	input 		[WIDTH-1:0] d7,
	output reg  [WIDTH-1:0] q7,
	input 	    [WIDTH-1:0] d8,
	output reg  [WIDTH-1:0] q8,
	input 		[WIDTH-1:0] d9,
	output reg  [WIDTH-1:0] q9,
	input 		[WIDTH-1:0] d10,
	output reg  [WIDTH-1:0] q10,
	input 		[WIDTH-1:0] d11,
	output reg  [WIDTH-1:0] q11,
	input 		[WIDTH-1:0] d12,
	output reg  [WIDTH-1:0] q12,
	input 		[WIDTH-1:0] d13,
	output reg  [WIDTH-1:0] q13,
	input 		[WIDTH-1:0] d14,
	output reg  [WIDTH-1:0] q14,
	input 		[WIDTH-1:0] d15,
	output reg  [WIDTH-1:0] q15);

	always @(posedge clk, posedge reset) begin
		if      (reset) q <= 0;
		else   
			begin	
				q <= d;
				q2 <= d2;
				q3 <= d3;
				q4 <= d4;
				q5 <= d5;
				q6 <= d6;			
				q7 <= d7;
				q8 <= q8;
				q9 <= q9;
				q10<= d10;
				q11<= d11;
				q12<= d12;
				q13<= d13;
				q14<= d14;
				q15<= d15;
			end
    end
endmodule

// Parameterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8) (
	input	[WIDTH-1:0]	d0, d1, 
	input				s, 
	output	[WIDTH-1:0]	y );

	assign y = s ? d1 : d0; 
endmodule

// Parameterized 3-to-1 MUX
module mux3 #(parameter WIDTH = 8) (
	input	[WIDTH-1:0]	d0, d1, d2 ,
	input	[1:0]		s, 
	output	reg [WIDTH-1:0]	y );

	always@(*) begin
	    case(s) 
	    	2'b00: y <= d0;
	    	2'b01: y <= d1;
	    	2'b10: y <= d2;
			default: y <= 32'bx;
	    endcase
	end
endmodule

// register file with one write port and three read ports
// the 3rd read port is for prototyping dianosis
module regfile(	
	input			clk, 
	input			we3, 
	input 	[ 4:0]	ra1, ra2, wa3, 
	input	[31:0] 	wd3, 
	output 	[31:0] 	rd1, rd2,
	input	[ 4:0] 	ra4,
	output 	[31:0] 	rd4);

	reg		[31:0]	rf[31:0];
	integer			n;
	
	//initialize registers to all 0s
	initial 
    begin
		for (n=0; n<32; n=n+1) 
			rf[n] = 32'h00;
        rf[29] = 32'h0000003C;
    end
			
	//write first order, include logic to handle special case of $0
    always @(negedge clk)
        if (we3)
			if (~ wa3[4])
				rf[{0,wa3[3:0]}] <= wd3;
			else
				rf[{1,wa3[3:0]}] <= wd3;
		
			// this leads to 72 warnings
			//rf[wa3] <= wd3;
			
			// this leads to 8 warnings
			//if (~ wa3[4])
			//	rf[{0,wa3[3:0]}] <= wd3;
			//else
			//	rf[{1,wa3[3:0]}] <= wd3;
		
	assign rd1 = (ra1 != 0) ? rf[ra1[4:0]] : 0;
	assign rd2 = (ra2 != 0) ? rf[ra2[4:0]] : 0;
	assign rd4 = (ra4 != 0) ? rf[ra4[4:0]] : 0;
endmodule

// Control Unit
module controller(
	input	[5:0]	op, funct,
	input			equalD,
	output			memtoreg, memwrite, pcsrc, alusrc, regdst, regwrite, 
	output          jump, jr, jal, multwrite, mflo, mfhi,
	                //added jr, jal, multwrite, mflo, mfhi signals
	output	[2:0]	alucontrol );

	wire	[1:0]	aluop;
	wire			branch;

	maindec	md(op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, jump,  
	           jal, aluop);
	aludec	ad(funct, aluop, alucontrol, jr, multwrite, mflo, mfhi);

	assign pcsrc = branch & equalD;
endmodule

// Data Path (excluding the instruction and data memories)
module datapath(
	input			clk, reset, memtoregD, pcsrcD, alusrcD, regdstD, regwriteD, jumpD, jrD, jalD, multwriteD, mfloD, mfhiD,
	input	[2:0]	alucontrolD,
	output			equalD,
	output	[31:0]	pc,
	input	[31:0]	instrF,
	output	[31:0]	aluoutE, 
	input	[31:0]	readdata,
	input	[ 4:0]	dispSel,
	output	[31:0]	dispDat,
    input           memwrite,
	output 			memwriteM
	);

	wire [4:0]  writereg;
	wire [4:0]  instrwriteaddr; //Added
	wire [31:0] pcnext, pcnextbr, pcplus4F, pcbranchD, pcnextj, signimmD, signimmshD, 
	            srca, srcb, result, P_Hi, P_Lo, result2, DataIn; //Added
	//Signals Added
	wire StallF, StallD, FlushE;
	wire [31:0] instrD, Outr1MuxD, Outr1MuxE, 
						Outr2MuxD, Outr2MuxE, 
						signimmE, 
						InLoE, InLoM, InLoW,
						InHiE, InHiM, InHiW,
						OutLoW, OutHiW,
						srcAE, srcBE,
						aluoutM, aluoutW,
						resultW,
						writedata, writedataM;
	wire [4:0]  writeregE, writeregM, writeregW,
				RsE, RtE;
	wire mfhiE, mfhiM, mfhiW,
		 mfloE, mfloM, mfloW,
		 multwriteE, multwriteM, multwriteW,
		 jrE, jumpE, jal, jalE,
		 regwrite, regwriteE, regwriteM, regwriteW,
		 memtoregE, memtoregM, memtoregW,
		 memwriteE, memwriteM,
		 alusrcE, regdstE,
		 forwardAD, forwardBD, forwardAE, forwardBE;
	wire [2:0] alucontrolE;
	
	// Fetching
	adder         pcadd1(pc, 32'b100, pcplus4F);
	mux2 #(32)    pcbrmux(pcplus4F, pcbranchD, pcsrcD, pcnextbr);
	mux2 #(32)    pcmux(pcnextbr, {pcplus4F[31:28], instrD[25:0], 2'b00}, jumpD, pcnextj);
	mux2 #(32)    pcjrmux(pcnextj, srca, jrD, pcnext);
	//F-Reg
	flopenr #(32) F_reg(clk, reset, StallF, pcnext, pc);  

	// Decoding
	// D-Reg				 clr     en      in1     out1    in2       out2
	flopenr2 #(32)D_Reg(clk, pcsrcD, StallD, instrF, instrD, pcplus4F, pcplus4D); 
	mux2 #(5)     jalAddrmux(writeregW, 5'b11111, jalE, writereg);
	mux2 #(32)    jalmux(resultW, pcplus4D, jalE, DataIn);
	signext	      se(instrD[15:0], signimmD);
	sl2           immsh(signimmD, signimmsh);
	adder         pcadd2(pcplus4D, signimmsh, pcbranchD);
    // register file logic
	regfile	      rf(clk, regwrite, instrD[25:21], instrD[20:16], writereg, DataIn, srca, r2DataIn, dispSel, dispDat);
	mux2 #(32)    forwardADmux(srca, aluoutM, forwardAD, Outr1MuxD);
	mux2 #(32)    forwardBDmux(r2DataIn, aluoutM, forwardBD, Outr2MuxD);
	assign equalD = (Outr1MuxD == Outr2MuxD) ? 1 : 0;
	//assign jal = (jalD && regwriteD) ?  1 : 0;
	//assign regwrite = (jal && regwriteW) ? 1 : 0;
	assign regwrite = ((jalD & regwriteD) | regwriteW) ? 1 : 0;

	// Executing 
	// E-Reg(top to bottom)	 clr     in1    out1   in2    out2   in3         out3 
	flopr15 #(32) E_Reg(clk, FlushE, mfhiD, mfhiE, mfloD, mfloE, multwriteD, multwriteE, 
				  //in4        out4       in5        out5       in6        out6 	
				    regwriteD, regwriteE, memtoregD, memtoregE, memwriteD, memwriteE,
				  //in7          out7	      in8      out8     in9      out9
				    alucontrolD, alucontrolE, alusrcD, alusrcE, regdstD, regdstE,
				  //in10       out10      in11       out11      in12	       out12
				    Outr1MuxD, Outr1MuxE, Outr2MuxD, Outr2MuxE, instrD[25:21], RsE,
			      //in13	       out13 in14		    out14 in15      out15
				    instrD[20:16], RtD,  instrD[15:11], RdE,  signimmD, signimmE);
	multiplier    MUL(Outr1MuxE, Outr2MuxE, InLoE, InHiE);
	mux3 #(32)    Emux1(Outr1MuxE, resultW, aluoutM, forwardBE, srcAE);
	mux3 #(32)    Emux2(Outr2MuxE, resultW, aluoutM, forwardAE, writedata);
	mux2 #(32)    alusrcmux(writedata, signimmE, alusrcE, srcBE);
	alu	          alu(srcaE, srcBE, alucontrolE, aluoutE);
	mux2 #(5)     wrmux(RtE, RdE, regdstE, writeregE);
		
	// Memory
	// M-Reg 						in1    out1   in2    out2   in3         out3
	flopr11 #(32) M_Reg(clk, reset, mfhiE, mfhiM, mfloE, mfloM, multwriteE, multwriteM,
				  //in4        out4       in5        out5       in6        out6
					regwriteE, regwriteM, memtoregE, memtoregM, memwriteE, memwriteM,
				  //in7    out7   in8    out8   in9      out9     in10        out10
					InLoE, InLoM, InHiE, InHiM, aluoutE, aluoutM, writedataE, writedataM, 
				  //in11       out11
					writeregE, writeregM);
	
	// Write
    // W-Reg		                in1    out1   in2    out2   in3         out3
	flopr10 #(32) W_Reg(clk, reset, mfhiM, mfhiW, mfloM, mfloW, multwriteM, multwriteW,
				  //in4        out4       in5        out5       in6    out6
					regwriteM, regwriteW, memtoregM, memtoregW, InLoM, InLoW,
			      //in7    out7   in8       out8       in9      out9     in10       out10
					InHiM, InHiW, readdata, readdataW, aluoutM, aluoutW, writeregM, writeregW);
    flopenr #(32) himem(clk, reset, multwriteW, InHiW, OutHiW); 
    flopenr #(32) lomem(clk, reset, multwriteW, InLoW, OutLoW); 
	// Result data cascased mux path to regfile WD3 input
	mux2 #(32)	  resmux(aluoutW, readdataW, memtoregW, result);
	mux2  #(32)   resormult(result, OutLoW, mfloW, result2); //Determines if DMem/AluOut xor LoOut is sent to RegFile.
    mux2  #(32)   dmux(result2, OutHiW, mfhiW, resultW);  //Determines if (DMem/AluOut xor LoOut) or HiOut is sent to RegFile.

	//Hazard Unit
	hazardUnit    (equalD, instrD[25:21], instrD[20:16], RsE, RtE, writeregE, writeregM, writeregW,
					memtoregE, memtoregM, regwriteE, regwriteM, regwriteW, StallF, StallD, FlushE,
					forwardAD, forwardBD, forwardBE, forwardAE);
endmodule

// The MIPS (excluding the instruction and data memories)
//Added jal, jr and "mult" signals
module mips(
	input        	clk, reset,
	output	[31:0]	pc,
	input 	[31:0]	instr,
	output			memwriteM,
	output	[31:0]	aluout, writedata,
	input 	[31:0]	readdata,
	input	[ 4:0]	dispSel,
	output	[31:0]	dispDat );

	wire 			memtoreg, branch, pcsrc, equalD, alusrc, regdst, regwrite, jump,
	                jr, jal, multwrite, mflo, mfhi; //Added
	wire	[2:0] 	alucontrol;

	controller c(instr[31:26], instr[5:0], equalD,
				memtoreg, memwrite, pcsrc,
				alusrc, regdst, regwrite, jump,
				jr, jal, multwrite, mflo, mfhi,
				alucontrol);
	datapath dp(clk, reset, memtoreg, pcsrc,
				alusrc, regdst, regwrite, jump,
				jr, jal, multwrite, mflo, mfhi,
				alucontrol, equalD, pc, instr, aluout, 
				readdata, dispSel, dispDat, memwrite, memwriteM);
endmodule

module hazardUnit (
	input 			branchD, 
	input [4:0]		RsD, RtD, RsE, RtE, writeregE, writeregM, writeregW,
	input 			memtoregE, memtoregM, regwriteE, regwriteM, regwriteW,
	output 			StallF, StallD, FlushE, 
					forwardAD, forwardBD, 
	output reg [1:0]forwardBE, forwardAE);
	
	wire branchstall, lwstall;
	
	/*
	Forwarding Logic
	ForwardAD = (rsD !=0) AND (rsD == WriteRegM) AND RegWriteM 
	ForwardBD = (rtD !=0) AND (rtD == WriteRegM) AND RegWriteM
	Stalling Logic
	branchstall = BranchD AND RegWriteE AND(WriteRegE == rsD OR WriteRegE == rtD)
					OR
					BranchD AND MemtoRegM AND(WriteRegM == rsD OR WriteRegM == rtD) 
	StallF = StallD = FlushE = lwstall OR branchstall
	lwstall = ((rsD == rtE) OR (rtD == rtE)) AND MemtoRegE
	forwardAE logic
		if ((rsE != 0) AND (rsE == WriteRegM) AND RegWriteM)
		then ForwardAE = 10
		else if ((rsE != 0) AND (rsE == WriteRegW) AND RegWriteW)
		then ForwardAE = 01 else ForwardAE = 00
	*/
	
	//Forwarding Logic
	assign forwardAD = ((RsD !== 0) & (RsD == writeregM) & (regwriteM)) ? 1 : 0;
	assign forwardBD = ((RtD !== 0) & (RtD == writeregM) & (regwriteM)) ? 1 : 0;
	
	always@(*) begin
		if ((RsE !== 0) & (RsE == writeregM) & (regwriteM))
			forwardAE = 2'b10;
		else if ((RsE !== 0) & (RsE == writeregM) & (regwriteW))
			forwardAE = 2'b01;
		else
			forwardAE = 2'b00;
	end
	
	always@(*) begin
		if ((RtE !== 0) & (RtE == writeregM) & (regwriteM))
			forwardBE = 2'b10;
		else if ((RtE !== 0) & (RtE == writeregM) & (regwriteW))
			forwardBE = 2'b01;
		else
			forwardBE = 2'b00;
	end	

	//Stalling Logic
	assign branchstall = (branchD & regwriteE & ((writeregE == RsD) | (writeregE == RtD)))
						 | 
						 (branchD & memtoregM & ((writeregM == RsD) | (writeregM == RtD)));
	assign lwstall = ((RsD == RtE) | (RtD == RtE)) & memtoregE;
	assign StallF = lwstall | branchstall;
	assign StallD = lwstall | branchstall;
	assign FlushE = lwstall | branchstall;
	
endmodule
	
// Instruction Memory
module imem (
	input	[ 5:0]	a,
	output 	[31:0]	dOut );
	
	reg		[31:0]	rom[0:63];
	
	//initialize rom from memfile_s.dat
	initial 
		$readmemh("memfile_s.dat", rom);
	
	//simple rom
    assign dOut = rom[a];
endmodule

// Data Memory
module dmem (
	input			clk,
	input			we,
	input	[31:0]	addr,
	input	[31:0]	dIn,
	output 	[31:0]	dOut );
	
	reg		[31:0]	ram[63:0];
	integer			n;
	
	//initialize ram to all FFs
	initial 
		for (n=0; n<64; n=n+1)
			ram[n] = 8'hFF;
		
	assign dOut = ram[addr[31:2]];
				
	always @(negedge clk)
		if (we) 
			ram[addr[31:2]] = dIn; 
endmodule
