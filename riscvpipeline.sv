module riscvpipeline (
    input 	  clk,
    input 	  reset,
    output [31:0] PC,
    input  [31:0] Instr,
    output [31:0] Address,  
    output [31:0] WriteData, 
    output        MemWrite,  
    input  [31:0] ReadData);

   /* The 10 "recognizers" for the 10 codeops */
   function isALUreg; input [31:0] I; isALUreg=(I[6:0]==7'b0110011); endfunction
   function isALUimm; input [31:0] I; isALUimm=(I[6:0]==7'b0010011); endfunction
   function isBranch; input [31:0] I; isBranch=(I[6:0]==7'b1100011); endfunction
   function isJALR;   input [31:0] I; isJALR  =(I[6:0]==7'b1100111); endfunction
   function isJAL;    input [31:0] I; isJAL   =(I[6:0]==7'b1101111); endfunction
   function isAUIPC;  input [31:0] I; isAUIPC =(I[6:0]==7'b0010111); endfunction
   function isLUI;    input [31:0] I; isLUI   =(I[6:0]==7'b0110111); endfunction
   function isLoad;   input [31:0] I; isLoad  =(I[6:0]==7'b0000011); endfunction
   function isStore;  input [31:0] I; isStore =(I[6:0]==7'b0100011); endfunction
   function isSYSTEM; input [31:0] I; isSYSTEM=(I[6:0]==7'b1110011); endfunction

   /* Register indices */
   function [4:0] rs1Id; input [31:0] I; rs1Id = I[19:15]; endfunction
   function [4:0] rs2Id; input [31:0] I; rs2Id = I[24:20]; endfunction
   function [4:0] shamt; input [31:0] I; shamt = I[24:20]; endfunction
   function [4:0] rdId;  input [31:0] I; rdId  = I[11:7];  endfunction
   function [1:0] csrId; input [31:0] I; csrId = {I[27],I[21]}; endfunction

   /* funct3 and funct7 */
   function [2:0] funct3; input [31:0] I; funct3 = I[14:12]; endfunction
   function [6:0] funct7; input [31:0] I; funct7 = I[31:25]; endfunction

   /* EBREAK and CSRRS instruction "recognizers" */
   function isEBREAK; input [31:0] I; isEBREAK = (isSYSTEM(I) && funct3(I) == 3'b000); endfunction

   /* The 5 immediate formats */
   function [31:0] Uimm; input [31:0] I; Uimm={I[31:12],{12{1'b0}}}; endfunction
   function [31:0] Iimm; input [31:0] I; Iimm={{21{I[31]}},I[30:20]}; endfunction
   function [31:0] Simm; input [31:0] I; Simm={{21{I[31]}},I[30:25],I[11:7]}; endfunction
   function [31:0] Bimm; input [31:0] I; Bimm = {{20{I[31]}},I[7],I[30:25],I[11:8],1'b0}; endfunction
   function [31:0] Jimm; input [31:0] I; Jimm = {{12{I[31]}},I[19:12],I[20],I[30:21],1'b0}; endfunction

   /* Read/Write tests */
   function writesRd; input [31:0] I; writesRd = !isStore(I) && !isBranch(I); endfunction
   function readsRs1; input [31:0] I; readsRs1 = !(isJAL(I) || isAUIPC(I) || isLUI(I)); endfunction
   function readsRs2; input [31:0] I; readsRs2 = isALUreg(I) || isBranch(I) || isStore(I); endfunction

/********************** F: Instruction fetch *********************************/
   localparam NOP = 32'b0000000_00000_00000_000_00000_0110011; // addi x0, x0, 0
   reg [31:0] F_PC;
   reg [31:0] FD_PC;
   reg [31:0] FD_instr;
   reg        FD_nop;
   assign PC = F_PC;
   
   /** These two signals come from the Execute stage **/
   wire [31:0] jumpOrBranchAddress;
   wire        jumpOrBranch;

   /** Stall signal logic (Load-Use Hazard) defined below but used here **/
   wire stall;

   always @(posedge clk) begin
      // PC Update Logic
      if (reset) begin
         F_PC <= 0;
      end else if (jumpOrBranch) begin
         // Flush: If taking a branch, go to target immediately
         F_PC <= jumpOrBranchAddress;
      end else if (!stall) begin
         // Normal operation: Next instruction
         F_PC <= F_PC + 4;
      end
      // If stalled, F_PC maintains value

      // Pipeline Register F -> D
      if (reset || jumpOrBranch) begin
         // Flush: Insert NOP if branching or resetting
         FD_instr <= NOP;
         FD_nop   <= 1'b1;
         FD_PC    <= 0;
      end else if (!stall) begin
         // Normal operation: Pass fetched instruction to Decode
         FD_instr <= Instr;
         FD_nop   <= 0;
         FD_PC    <= F_PC;
      end
      // If stalled, FD_instr maintains value (Decode stage repeats/holds)
   end

/************************ D: Instruction decode *******************************/
   reg [31:0] DE_PC;
   reg [31:0] DE_instr;
   reg [31:0] DE_rs1;
   reg [31:0] DE_rs2;
   /* These three signals come from the Writeback stage */
   wire        writeBackEn;
   wire [31:0] writeBackData;
   wire [4:0]  wbRdId;

   reg [31:0] RegisterBank [0:31];

   always @(posedge clk) begin
      // Pipeline Register D -> E
      if (reset || jumpOrBranch || stall) begin
          // Flush (Branch) OR Bubble (Stall): Insert NOP into Execute
          DE_instr <= NOP;
          DE_PC    <= 0; 
          DE_rs1   <= 0;
          DE_rs2   <= 0;
      end else begin
          DE_PC    <= FD_PC;
          DE_instr <= FD_nop ? NOP : FD_instr;
          
          // Register Read with Write-Bypass (Step 2 of README / "Same Cycle")
          // If WB stage is writing to the same register we are reading, use the new data.
          DE_rs1 <= rs1Id(FD_instr) ? 
                    ((writeBackEn && wbRdId == rs1Id(FD_instr) && wbRdId != 0) ? writeBackData : RegisterBank[rs1Id(FD_instr)]) 
                    : 32'b0;
          
          DE_rs2 <= rs2Id(FD_instr) ? 
                    ((writeBackEn && wbRdId == rs2Id(FD_instr) && wbRdId != 0) ? writeBackData : RegisterBank[rs2Id(FD_instr)]) 
                    : 32'b0;
      end

      // Writeback (Happens at posedge, standard)
      if (writeBackEn)
          RegisterBank[wbRdId] <= writeBackData;
   end

/************************ E: Execute *****************************************/
   reg [31:0] EM_PC;
   reg [31:0] EM_instr;
   reg [31:0] EM_rs2;
   reg [31:0] EM_Eresult;
   reg [31:0] EM_addr;
   
   // Signals for Hazard/Forwarding from M and W stages
   wire [31:0] MW_instr; // From W stage
   
   // --- Forwarding Unit (Step 1 of README) ---
   // Check M stage (EM_instr) and W stage (MW_instr) for dependencies
   wire forwardA_M = (writesRd(EM_instr) && rdId(EM_instr) != 0 && rdId(EM_instr) == rs1Id(DE_instr));
   wire forwardA_W = (writesRd(MW_instr) && rdId(MW_instr) != 0 && rdId(MW_instr) == rs1Id(DE_instr));
   wire forwardB_M = (writesRd(EM_instr) && rdId(EM_instr) != 0 && rdId(EM_instr) == rs2Id(DE_instr));
   wire forwardB_W = (writesRd(MW_instr) && rdId(MW_instr) != 0 && rdId(MW_instr) == rs2Id(DE_instr));

   // Select Forwarded Data (M stage has priority as it's more recent)
   // Note: If M is Load, stall logic handles it. If M is ALU, data is in EM_Eresult.
   // For W, data is in writeBackData.
   wire [31:0] forwarded_rs1 = forwardA_M ? EM_Eresult : (forwardA_W ? writeBackData : DE_rs1);
   wire [31:0] forwarded_rs2 = forwardB_M ? EM_Eresult : (forwardB_W ? writeBackData : DE_rs2);

   // Use forwarded values for ALU
   wire [31:0] E_aluIn1 = forwarded_rs1;
   wire [31:0] E_aluIn2 = isALUreg(DE_instr) | isBranch(DE_instr) ? forwarded_rs2 : Iimm(DE_instr);
   
   wire [4:0]  E_shamt  = isALUreg(DE_instr) ? forwarded_rs2[4:0] : shamt(DE_instr); // Corrected to use forwarded rs2
   wire E_minus = DE_instr[30] & isALUreg(DE_instr);
   wire E_arith_shift = DE_instr[30];
   
   // --- Stall Unit (Step 3 of README) ---
   // Detect Load-Use Hazard: Prev instruction (now in E, 'DE_instr' is current? No.)
   // Wait: DE_instr is the instruction currently in Execute. FD_instr is the one in Decode.
   // The hazard is if DE_instr (Execute) is a Load, and FD_instr (Decode) needs that value.
   assign stall = isLoad(DE_instr) && (
                     (readsRs1(FD_instr) && rs1Id(FD_instr) == rdId(DE_instr)) ||
                     (readsRs2(FD_instr) && rs2Id(FD_instr) == rdId(DE_instr))
                  ) && rdId(DE_instr) != 0;

   // The adder is used by both arithmetic instructions and JALR.
   wire [31:0] E_aluPlus = E_aluIn1 + E_aluIn2;
   // Use a single 33 bits subtract to do subtraction and all comparisons
   wire [32:0] E_aluMinus = {1'b1, ~E_aluIn2} + {1'b0,E_aluIn1} + 33'b1;
   wire        E_LT  = (E_aluIn1[31] ^ E_aluIn2[31]) ? E_aluIn1[31] : E_aluMinus[32];
   wire        E_LTU = E_aluMinus[32];
   wire        E_EQ  = (E_aluMinus[31:0] == 0);

   // Flip a 32 bit word.
   function [31:0] flip32;
      input [31:0] x;
      flip32 = {x[ 0], x[ 1], x[ 2], x[ 3], x[ 4], x[ 5], x[ 6], x[ 7],
		x[ 8], x[ 9], x[10], x[11], x[12], x[13], x[14], x[15],
		x[16], x[17], x[18], x[19], x[20], x[21], x[22], x[23],
		x[24], x[25], x[26], x[27], x[28], x[29], x[30], x[31]};
   endfunction

   wire [31:0] E_shifter_in = funct3(DE_instr) == 3'b001 ? flip32(E_aluIn1) : E_aluIn1;
   wire [31:0] E_shifter = $signed({E_arith_shift & E_aluIn1[31], E_shifter_in}) >>> E_aluIn2[4:0];
   wire [31:0] E_leftshift = flip32(E_shifter);

   reg [31:0] E_aluOut;
   always @(*) begin
      case(funct3(DE_instr))
         3'b000: E_aluOut = E_minus ? E_aluMinus[31:0] : E_aluPlus;
         3'b001: E_aluOut = E_leftshift;
         3'b010: E_aluOut = {31'b0, E_LT};
         3'b011: E_aluOut = {31'b0, E_LTU};
         3'b100: E_aluOut = E_aluIn1 ^ E_aluIn2;
         3'b101: E_aluOut = E_shifter;
         3'b110: E_aluOut = E_aluIn1 | E_aluIn2;
         3'b111: E_aluOut = E_aluIn1 & E_aluIn2;
      endcase
   end

   /*********** Branch, JAL, JALR ***********************************/
   reg E_takeBranch;
   always @(*) begin
      case (funct3(DE_instr))
         3'b000: E_takeBranch = E_EQ;
         3'b001: E_takeBranch = !E_EQ;
         3'b100: E_takeBranch = E_LT;
         3'b101: E_takeBranch = !E_LT;
         3'b110: E_takeBranch = E_LTU;
         3'b111: E_takeBranch = !E_LTU;
         default: E_takeBranch = 1'b0;
      endcase
   end

   wire E_JumpOrBranch = (
         isJAL(DE_instr)  ||
         isJALR(DE_instr) ||
         (isBranch(DE_instr) && E_takeBranch)
   );
   wire [31:0] E_JumpOrBranchAddr =
	isBranch(DE_instr) ? DE_PC + Bimm(DE_instr) :
	isJAL(DE_instr)    ? DE_PC + Jimm(DE_instr) :
	/* JALR */           {E_aluPlus[31:1],1'b0} ;

   wire [31:0] E_result =
	(isJAL(DE_instr) | isJALR(DE_instr)) ? DE_PC+4                :
	isLUI(DE_instr)                      ? Uimm(DE_instr)         :
	isAUIPC(DE_instr)                    ? DE_PC + Uimm(DE_instr) :
                                          E_aluOut               ;

   always @(posedge clk) begin
      EM_PC      <= DE_PC;
      EM_instr   <= DE_instr;
      // Pass the forwarded value of rs2 to Memory stage (crucial for SW instructions!)
      EM_rs2     <= forwarded_rs2; 
      EM_Eresult <= E_result;
      EM_addr    <= isStore(DE_instr) ? forwarded_rs1 + Simm(DE_instr) : // Use forwarded rs1 for address
                                        forwarded_rs1 + Iimm(DE_instr) ;
   end

/************************ M: Memory *******************************************/
   reg [31:0] MW_PC;
   // MW_instr declared below (reg) but used in forwarding logic above (wire logic)
   // To fix Verilog scoping, we need to access the reg.
   // SystemVerilog allows this.
   reg [31:0] MW_instr_reg;
   assign MW_instr = MW_instr_reg; // Drive the wire used in Forwarding

   reg [31:0] MW_Eresult;
   reg [31:0] MW_addr;
   reg [31:0] MW_Mdata;
   reg [31:0] MW_IOresult;
   reg [31:0] MW_CSRresult;
   wire [2:0] M_funct3 = funct3(EM_instr);
   wire M_isB = (M_funct3[1:0] == 2'b00);
   wire M_isH = (M_funct3[1:0] == 2'b01);
   
   // Halt logic based on Writeback stage instruction (completed)
   // Wait, original code checked 'MW_instr'.
   assign halt = !reset & isEBREAK(MW_instr);

   /*************** STORE **************************/
   wire [31:0] M_STORE_data = EM_rs2;
   assign Address  = EM_addr;
   assign MemWrite    = isStore(EM_instr);
   assign WriteData = EM_rs2;

   always @(posedge clk) begin
      MW_PC        <= EM_PC;
      MW_instr_reg <= EM_instr;
      MW_Eresult   <= EM_Eresult;
      MW_Mdata     <= ReadData;
      MW_addr      <= EM_addr;
   end

/************************ W: WriteBack ****************************************/

   wire [2:0] W_funct3 = funct3(MW_instr);
   wire W_isB = (W_funct3[1:0] == 2'b00);
   wire W_isH = (W_funct3[1:0] == 2'b01);
   wire W_sext = !W_funct3[2];
   wire W_isIO = MW_addr[22];

   /*************** LOAD ****************************/
   assign writeBackData = isLoad(MW_instr) ? MW_Mdata : MW_Eresult;
   assign writeBackEn = writesRd(MW_instr) && rdId(MW_instr) != 0;
   assign wbRdId = rdId(MW_instr);

   assign jumpOrBranchAddress = E_JumpOrBranchAddr;
   assign jumpOrBranch        = E_JumpOrBranch;

   /******************************************************************************/

   always @(posedge clk) begin
      if (halt) begin
         $writememh("regs.out", RegisterBank);
         $finish();
      end
   end
endmodule