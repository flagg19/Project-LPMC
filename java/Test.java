
import org.antlr.runtime.*;
import java.io.*;
import java.util.HashMap;

class Test {

    public static void main(String[] args) throws Exception {
      
        FunctionalLanguageLexer lex = new FunctionalLanguageLexer(new ANTLRFileStream(args[0]));
        CommonTokenStream tokens = new CommonTokenStream(lex);
        FunctionalLanguageParser parser = new FunctionalLanguageParser(tokens);
        
        
        
        HashMap result = parser.prog();
        
        if(result.get(1).equals("ERROR"))
        {
          System.out.println("#######################");
          System.out.println("# ERRORI DI PARSING!! #");
          System.out.println("#######################");
          
          for(int i=2;i<result.size();i++)
          {
            System.out.println("\nERRORI AL COMANDO #" + result.get(i).toString());
          }
        }
        else
        {
          FileWriter fstream = new FileWriter(args[0]+".asm");
          
          fstream.write(result.get(0).toString());
          fstream.close();
          
          StackVirtualMachineLexer lex2 = new StackVirtualMachineLexer(new ANTLRFileStream(args[0]+".asm"));
          CommonTokenStream tokens2 = new CommonTokenStream(lex2);
          StackVirtualMachineParser parser2 = new StackVirtualMachineParser(tokens2);
         
          boolean debug = false;
          
          if(args.length>1)
          {
             if(args[1].equals("d"))
             {
               debug = true;
             }
             else
             {
               debug = false;
             }
          }
          
          SVM m = new SVM(parser2.createCode(),debug);
          
          m.run();
        }
    }
}
