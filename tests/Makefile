# http://iverilog.icarus.com/
CC=iverilog 
FLAGS=-Wall -g2012
# http://gtkwave.sourceforge.net/
VIEWER=code
# http://gtkwave.sourceforge.net/
# VIEWER=gtkwave
# https://github.com/yne/vcd
# VIEWER=../../../vcd/vcd < 
# https://drom.io/vcd/?github=menotti/up1/master/processor/dump.vcd

# Toolchain
CROSS   = riscv64-unknown-elf
AS      = $(CROSS)-as
LD      = $(CROSS)-ld
OBJCOPY = $(CROSS)-objcopy
OBJDUMP = $(CROSS)-objdump

# Arquivos
LDS    = riscv.ld
SRC    = riscv.asm
OBJ    = $(SRC:.asm=.o)
ELF    = riscv.elf
LST    = riscv.lst
HEX_TEXT = text.hex
HEX_DATA = data.hex

all: $(HEX_TEXT) $(HEX_DATA) $(LST) simul

# Monta o assembly (RV32)
$(OBJ): $(SRC)
	$(AS) -march=rv32i -o $@ $<

# Linka em 32 bits usando o linker script
$(ELF): $(OBJ) $(LDS)
	$(LD) -m elf32lriscv -T $(LDS) -o $@ $<

# Gera HEX de instruções (.text) (memória Harvard)
$(HEX_TEXT): $(ELF)
	$(OBJCOPY) -O verilog --verilog-data-width=4 \
	--only-section=.text $< $@

# Gera HEX de dados (.data + .bss) (memória Harvard)
$(HEX_DATA): $(ELF)
	$(OBJCOPY) -O verilog --verilog-data-width=4 \
	--change-section-lma .data=0x0 --change-section-lma .bss=0x0 \
	--only-section=.data --only-section=.bss $< $@

# Gera listagem com instruções + dados
$(LST): $(ELF)
	$(OBJDUMP) -D $< > $@
	@echo "Listagem gerada em $(LST)"

clean:
	rm -f $(OBJ) $(ELF) $(HEX) $(HEX_TEXT) $(HEX_DATA) $(LST) *.out dump.vcd dump.log riscv.asm

simul: *.sv ../*.sv
	$(CC) -D$(VERSION) $(FLAGS) ../*.sv *.sv 
# 	vvp a.out | grep -v xxxx | sort > dump.log
# 	vvp a.out > dump.log
	vvp a.out 
# 	$(VIEWER) dump.vcd
# 	$(VIEWER) dump.vcd config.gtkw