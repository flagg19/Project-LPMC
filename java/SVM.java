public class SVM {
  
  
  private boolean debug = false;
  private static final int MEMSIZE = 10000;
  private static final int STATICSIZE = 1000;
  private static final int MAXRECURSION = 1000;
  private final static int ERRORS = -9999;
  
  private int[] code;
  private int[] memory = new int[MEMSIZE];
  
  private int ir = 0;
  private int sp = MEMSIZE;
  private int fp = MEMSIZE;
  private int hp = STATICSIZE;
  private int raPtr = 0;
  private int[] ra = new int[MAXRECURSION];
  private int rv = 0;
  private int al = MEMSIZE;
  
  private String stampInfo()
  {
    String res = "IR: " + ir + ", SP: " + sp + ", FP:" + fp + ", HP: " + hp + ", RA: " + ra + ", RV: " +rv + ",AL: " + al + "\n";
    return res;
  }
  
  public SVM(int[] instructions, boolean debug) {
    this.debug = debug;
    this.ra[raPtr] = 0;
    
    code = instructions;
      if(debug)
      {
        int i=0;
        while(i<102)
        {
          System.out.print(code[i++] + " ");
        }
        System.out.println();
      }
  }
  
  public void run() {
    while (ir < code.length) {
        int bytecode = code[ir++];
        //Cancella
        if(debug)
          System.out.print(ir-1 + ": " + code[ir-1] + " - ");
        
        switch (bytecode) {
          case StackVirtualMachineParser.PUSH:
            push(code[ir++]);
            //Cancella
            if(debug)
              System.out.println("push di code[ir] = "+code[ir-1]+" sullo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.POP:
            pop();
            //Cancella
            if(debug)
              System.out.println("pop " + stampInfo());
            break;
          case StackVirtualMachineParser.DUPLICATE:
            int top = pop();
            push(top);
            push(top);
            //Cancella
            if(debug)
              System.out.println("Duplico la cima dello stack " + stampInfo());
            break;
          case StackVirtualMachineParser.ADD:
            push(pop()+pop());
            //Cancella
            if(debug)
              System.out.println("somma " + stampInfo());
            break; 
          case StackVirtualMachineParser.SUB:
            push(pop()-pop());
            //Cancella
            if(debug)
              System.out.println("sottrazione " + stampInfo());
            break;
          case StackVirtualMachineParser.MUL:
            push(pop()*pop());
            //Cancella
            if(debug)
              System.out.println("moltiplicazione " + stampInfo());
            break;
          case StackVirtualMachineParser.LOADW: 
            int pos = pop();
            push(memory[pos]);
            //Cancella
            if(debug)
              System.out.println("lw: memory["+pos+"]="+memory[pos]+" sullo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STOREW: 
            int add = pop();
            memory[add] = pop();
            //Cancella
            if(debug)
              System.out.println("sw: memory["+add+"]="+memory[add]+"dallo stack " + stampInfo());
            break;   
          case StackVirtualMachineParser.LOADFP: 
            push(fp);
            //Cancella
            if(debug)
              System.out.println("lfp: inserisco fp in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STOREFP: 
            fp = pop();
            //Cancella
            if(debug)
              System.out.println("sfp: recupero fp dallo stack " + stampInfo());
            break;  
          case StackVirtualMachineParser.LOADSP: 
            push(sp);
            //Cancella
            if(debug)
              System.out.println("lsp: inserisco sp in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STORESP: 
            sp = pop();
            //Cancella
            if(debug)
              System.out.println("ssp: sp = cima dello stack " + stampInfo());
            break;   
          case StackVirtualMachineParser.LOADHP: 
            push(hp);
            //Cancella
            if(debug)
              System.out.println("lhp: inserisco hp in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STOREHP: 
            hp = pop();
            //Cancella
            if(debug)
              System.out.println("shp: hp = cima dello stack " + stampInfo());
            break;   
          case StackVirtualMachineParser.LOADRA: 
            push(ra[raPtr]);
            //Cancella
            if(debug)
              System.out.println("lra: inserisco ra in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STORERA: 
            ra[raPtr] = pop();
            //Cancella
            if(debug)
              System.out.println("sra: ra = cima dello stack " + stampInfo());
            break;
          case StackVirtualMachineParser.LOADRV: 
            push(rv);
            //Cancella
            if(debug)
              System.out.println("lrv: inserisco rv in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STORERV: 
            rv = pop();
            //Cancella
            if(debug)
              System.out.println("srv: rv = cima dello stack " + stampInfo());
            break;   
          case StackVirtualMachineParser.LOADAL: 
            push(al);
            //Cancella
            if(debug)
              System.out.println("lal: inserisco al in cima allo stack " + stampInfo());
            break;
          case StackVirtualMachineParser.STOREAL: 
            al = pop();
            //Cancella
            if(debug)
              System.out.println("sal: al = cima dello stack " + stampInfo());
            break;
          case StackVirtualMachineParser.CHAINAL: 
            pos = pop();
            push(memory[pos-1]);
            //Cancella
            if(debug)
            {
              System.out.println("Inserisco in cima allo stack memory[AL-1] = " + memory[pos-1] + " " + stampInfo());
              //System.out.println("Inserisco in cima allo stack memory[AL] = " + memory[pos] + " " + stampInfo());
              //System.out.println("Inserisco in cima allo stack memory[AL+1] = " + memory[pos+1] + " " + stampInfo());
            }
            break;
          case StackVirtualMachineParser.BRANCH: 
            add = code[ir++];
            ir=add;
            //Cancella
            if(debug)
              System.out.println("salto incondizionato " + stampInfo());
            break;   
          case StackVirtualMachineParser.BRANCHEQ: 
            add = code[ir++];
            int a = pop();
            int b = pop();
            if ( a == b ) ir=add;
            //Cancella
            if(debug)
              System.out.println("salto se uguale "+a+", "+b+" " + stampInfo());
            break;  
          case StackVirtualMachineParser.BRANCHLESS: 
            add = code[ir++];
            int c = pop();
            int d = pop();
            if ( c < d ) ir=add;
            //Cancella
            if(debug)
              System.out.println("salto se minore "+c+","+d+" " + stampInfo());
            break;  
          case StackVirtualMachineParser.JAL: 
            raPtr++;
            ra[raPtr] = ir+1;
            ir = code[ir];
            //Cancella
            if(debug)
              System.out.println("salto a funzione. " + stampInfo());
            break;  
          case StackVirtualMachineParser.JALN: 
            raPtr++;
            ra[raPtr] = ir+1;
            ir = code[ir];
            //Cancella
            if(debug)
              System.out.println("salto a funzione definita localmente. " + stampInfo());
            break;  
          case StackVirtualMachineParser.JRA: 
            ir = ra[raPtr];
            raPtr--;
            //Cancella
            if(debug)
              System.out.println("recupero il valore di return address ("+ir+"). " + stampInfo());
            break; 
          case StackVirtualMachineParser.PRINT:
            //Cancella
            if(debug)
          {
            System.out.print("Stampa del programma: ");
            System.out.println(pop()+" " + stampInfo());
          }
            else
            {
              System.out.println(pop());
            }
            break;
          case StackVirtualMachineParser.PRINTB:
            //Cancella
            int v = pop();
          String msg = (v==0?"FALSO":"VERO");
          if(debug)
          {
            System.out.print("Stampa del programma: ");
            System.out.println(msg+" " + stampInfo());
          }
          else
          {
            System.out.println(msg);
          }
          break;
          case StackVirtualMachineParser.HALT:
            //Cancella
            if(debug)
            System.out.println("Termine programma. " + stampInfo());
            return;          
        }  
      }
  }
  
  private int pop() {
    return memory[sp++]; 
  }
  
  private void push(int b) {
    memory[--sp] = b; 
  }
}