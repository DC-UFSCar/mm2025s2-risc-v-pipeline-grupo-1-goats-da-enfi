module testbench();
  logic        clk, reset, memwrite;
  logic [31:0] pc, instr;
  logic [31:0] writedata, addr, readdata;
    
  // microprocessor
  riscvpipeline cpu(clk, reset, pc, instr, addr, writedata, memwrite, readdata);

  // instructions memory 
  mem #("text.hex") instr_mem(.clk(clk), .a(pc), .rd(instr));

  // data memory 
  mem #("data.hex") data_mem(clk, memwrite, addr, writedata, readdata);

  // initialize test
  initial
    begin
      $dumpfile("dump.vcd"); $dumpvars(0);
      reset <= 1; #15 reset <= 0;
      //$monitor("%3t PC=%h instr=%h aluIn1=%h aluIn2=%h addr=%h writedata=%h memwrite=%b readdata=%h writeBackData=%h", $time, pc, instr, cpu.aluIn1, cpu.aluIn2, addr, writedata, memwrite, readdata, cpu.writeBackData);
      #1000;
      $writememh("regs.out", cpu.RegisterBank);
      $finish;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end
endmodule