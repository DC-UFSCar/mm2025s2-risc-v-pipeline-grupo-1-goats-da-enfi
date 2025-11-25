cd tests
echo "Testando o programa $1.asm ..." 
cp $1.asm riscv.asm               # Copia o arquivo de teste
rm -f a.out regs.out              # Limpa arquivos antigos      
make                                            # Simula o processador
./a.out                                         # Executa o teste       

if diff regs.out $1.ok >/dev/null; then   # Compara com a saída esperada
    echo "OK"
else
    echo "ERRO: saída incorreta"
    echo "ESPERADA:"
    head $1.ok
    echo "OBTIDA:"
    cat regs.out
    exit 1
fi
