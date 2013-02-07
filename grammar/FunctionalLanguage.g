grammar FunctionalLanguage;

@header {
	import java.util.HashMap;
	import java.util.Map;
}

@members {
	//Costanti
	private final static int PARAM = 0;
	private final static int TRUEVAR = 1;
	private final static int FUNC = 2;
	private final static int LOCFUNC = 3;
	private final static int TRUEVALUE = 1;
	private final static int FALSEVALUE = 0;
	private final static int EMPTYVALUE = -1;
	private final static int TYPE = 1;
	private final static int CODE = 0;
	
	//Strutture dati di appoggio alla SDT
	private int staticData = 0;
	private int labelCounter = 0;
	private List<Integer> parameterCounter = new ArrayList<Integer>();
	private List<HashMap> symTable = new ArrayList<HashMap>();
	private int nestLevel = 0;
	private List<String> functionCode = new ArrayList<String>();
	private int numErrors = 2; //inizializzato a 2, per cominciare a scrivere da dopo [codice/typeFinale] ovvero le info che prog restituisce
	private int row = 1; //Conteggio delle righe per dare indicazioni su dove avvengano errori (per esempio di type mismatch)
	String removePar = "";
	String currFuncType = "";
	int numIfThenNest = 0;
	private int numPar = 0; //Uso in controlli numero parametri passati alle funzioni
	private int numCicli = 0;
	private int numFunzione = 0; //per disambiguare in maniera univoca le funzioni
	private boolean primoParMancante = true;
	private boolean errors = false;
	private List<String> listoferrors = new ArrayList<String>();
	
	//Classe per la memorizzazione dei simboli (riferimento, tipo, lista parametri [eventuale]) 
	private class SymTableEntry 
	{
		int ref;
		public String name;
		String type; //per la funzione è il tipo di ritorno, per una variabile il tipo specifico
		int category;
		public int nestLvl;
		int id;
		public List<String> paramTypeList;
		
		public SymTableEntry(int r, String t, int cat, int nestLvl, String name)
		{
			this.ref = r;
			this.type = t;
			this.category = cat;
			this.nestLvl = nestLvl;
			this.name = name;
		} 
		public int Ref()
		{
			return this.ref;
		}
		public String Type()
		{
			return this.type;
		}
		public int Category()
		{
			return this.category;
		}
		public void pushParamType(String s)
		{
			if(paramTypeList == null)
			{
				paramTypeList = new ArrayList<String>();
			}
			
			paramTypeList.add(s);
		} 
		public void setID(int id)
		{
			this.id = id;
		}
		public int ID()
		{
			return this.id;
		}
	}	
}

//PARSER

prog returns [HashMap results]
	@init {
		results = new HashMap();
		$results.put(CODE,""); 
		$results.put(TYPE,"");
		errors = false;
	}
	:
		((p = expr
		{
			listoferrors.add("");
			results.put(CODE,$results.get(CODE) + $p.code[CODE]+"\n"); 
	  				
			if($p.code[TYPE]==null || $p.code[CODE]==null || $p.code[TYPE].equals("ERROR")) 
			{
				$results.put(TYPE, "ERROR"); 
				$results.put(numErrors++,row + "\n" + listoferrors.get(row-1));
				errors = true;
			}
			if(!errors)
			{
				$results.put(TYPE,$p.code[TYPE]); 
			}
			row++;
	  		}
		| c = definition
		{
			listoferrors.add("");
			//System.out.println($c.code[TYPE]);
			if($c.code[TYPE]==null || $c.code[CODE]==null || $c.code[TYPE].toString().equals("ERROR"))
			{
				$results.put(TYPE, "ERROR");
				$results.put(numErrors++,row + "\n" + listoferrors.get(row-1));
				errors = true;
			}
			if(!errors)
			{
				$results.put(TYPE,$c.code[TYPE]); 
			}
			$results.put(CODE,$results.get(CODE) + $c.code[CODE]+"\n"); 
			row++;
		}
		)SEMIC)+
		{
			String tmp = "";
			for(int ii=0;ii<functionCode.size();ii++)
			{
				tmp += functionCode.get(ii).toString();
			}
			$results.put(CODE,$results.get(CODE) + "\thalt\n\n\n"+tmp); 
		}
	;
	catch [RecognitionException re] {reportError(re);}

definition returns [String[\] code]
	@init {
		code = new String[3];
		symTable.add(new HashMap());
	}
	:
		cc=command {$code = $cc.code;}
		| ty=TYP i=ID ASS e=expr 
		{	
			$code[TYPE] = "";
			if (symTable.get(nestLevel).get($i.text.toString()) == null) 
			{
				if(nestLevel-numIfThenNest==0) //ambitoGlobale
				{
					symTable.get(nestLevel).put($i.text.toString(),new SymTableEntry(new Integer(staticData),$ty.text.toUpperCase(),TRUEVAR,nestLevel-numIfThenNest,$i.text));
					$code[CODE] = $e.code[CODE] + "\tpush "+(staticData++)+"\n"+"\tsw\n";
				}
				else //ambito locale
				{
					symTable.get(nestLevel).put($i.text.toString(),new SymTableEntry(new Integer(parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0))),$ty.text.toUpperCase(),PARAM,nestLevel-numIfThenNest,$i.text));
					String riposizionaNuovaVar = "";
					for(int jj=parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0))-1;jj>0;jj--) 
					{
						riposizionaNuovaVar += 
							"\tdup\n" + //duplics la cima dello stack
							"\tlfp\n" + 
							"\tpush " + jj + "\n" +
							"\tadd\n" +
							"\tlw\n" + //recupero l'i-simo parametro a partire dall'ultimo
							"\tlfp\n" + 
							"\tsw\n" + //inserisco il parametro recuperato alla cella puntata da FP
							"\tpush " + jj + "\n" + //inserisco l'indice del parametro recuperato
							"\tlfp\n" +
							"\tadd\n" +
							"\tsw\n"; //inserisco il nuovo valore al posto del parametro recuperato
					}
					$code[CODE] =
						"\tpop\n" + //toglie AL
						"\tpop\n" + //toglie RA
						$e.code[CODE] + //inserisce il nuovo valore
						riposizionaNuovaVar +
						"\tlra\n" + //rimette RA
						"\tlal\n" + //rimette AL
						"\tpush 1\n" + //Sposto FP in su di 1 (in realtà in giù perchè lo stack cresce al contrario)
						"\tlfp\n" + 
						"\tsub\n" +
						"\tsfp\n";  
					parameterCounter.set(Math.max(nestLevel-1-numIfThenNest,0),parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0)) + 1);
				}
				
				if($e.code[TYPE]==null || !$e.code[TYPE].equals($ty.text.toUpperCase())) 
				{
					if(listoferrors.size()<row)
					{
						listoferrors.add($i.text + " : viene assegnato un tipo scorretto.\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + " : viene assegnato un tipo scorretto.\n");
					}
					$code[TYPE] = "ERROR";
				} 
				else 
				{
					$code[TYPE] = $ty.text.toUpperCase();
				}
			} 
			else 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add($i.text + " : variabile già dichiarata.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + " : variabile già dichiarata.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| DEF ty=TYP i=ID LPAR 
		{
			String check = "";
			numFunzione++;
			
			if(parameterCounter.size() <= (nestLevel-numIfThenNest))
			{
				parameterCounter.add(1);
			}
			else
			{
				parameterCounter.set(nestLevel-numIfThenNest,1);
			}
			if (symTable.get(nestLevel).get($i.text.toString()) == null && symTable.get(nestLevel>0?nestLevel-1:0).get($i.text.toString()) == null) 
			{
				symTable.add(new HashMap());
				if(nestLevel>0)
				{
					symTable.get(nestLevel++).put($i.text.toString(),new SymTableEntry(new Integer(staticData),$ty.text.toUpperCase(),LOCFUNC,nestLevel,$i.text));
				}
				else
				{
					symTable.get(nestLevel++).put($i.text.toString(),new SymTableEntry(new Integer(staticData),$ty.text.toUpperCase(),FUNC,nestLevel,$i.text));
				}
				((SymTableEntry)(symTable.get(nestLevel-1).get($i.text))).setID(numFunzione);
			} 
			else 
			{	
				if(listoferrors.size()<row)
				{
					listoferrors.add($i.text + " : funzione già dichiarata.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + " : funzione già dichiarata.\n");
				}
				check = "ERROR";
			}
		}
		(typ=TYP j=ID 
		{
			symTable.get(nestLevel).put($j.text,new SymTableEntry(new Integer(parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0))),$typ.text.toUpperCase(),PARAM,nestLevel,$i.text));
			parameterCounter.set(Math.max(nestLevel-1-numIfThenNest,0),parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0)) + 1);
			((SymTableEntry)symTable.get(Math.max(nestLevel-1,0)).get($i.text)).pushParamType($typ.text.toUpperCase());
		}
		(COMMA typ=TYP j=ID 
		{
			if (symTable.get(nestLevel).get($j.text.toString()) == null) 
			{
				symTable.get(nestLevel).put($j.text,new SymTableEntry(new Integer(parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0))),$typ.text.toUpperCase(),PARAM,nestLevel,$i.text));
				parameterCounter.set(Math.max(nestLevel-1-numIfThenNest,0),parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0)) + 1);
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add($j.text + " : parametro già dichiarato.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + $j.text + " : parametro già dichiarato.\n");
				}
				check = "ERROR";
			}
			((SymTableEntry)symTable.get(Math.max(nestLevel-1,0)).get($i.text)).pushParamType($typ.text.toUpperCase());
		}
		)*)?RPAR LBPAR
		{
			if(functionCode.size()<nestLevel)//livello annidamento non ancora raggiunto
			{
				functionCode.add( 
					"func" + numFunzione +  $i.text+":\n" + 
					"\tlsp\n"+
					"\tsfp\n"+
					"\tsal\n" + //prendo al e lo reiserisco nello stack sopra al return address (con lal)
					"\tlra\n" +
					"\tlal\n");
			}
			else
			{
				if(!check.equals("ERROR"))
				{
				functionCode.set(Math.max(nestLevel-1,0),
					functionCode.get(Math.max(nestLevel-1,0)) + 
					"func"+ numFunzione  + $i.text+":\n" + 
					"\tlsp\n"+
					"\tsfp\n"+
					"\tsal\n" + //prendo al e lo reiserisco nello stack sopra al return address (con lal)
					"\tlra\n" +
					"\tlal\n");
				}
			}
		}
		((e=definition 
		{
			if(functionCode.size()<nestLevel)//livello appena raggiunto
			{
				functionCode.add($e.code[CODE]);
			}
			else
			{
				if(!check.equals("ERROR"))
				{
					functionCode.set(Math.max(nestLevel-1,0),functionCode.get(Math.max(nestLevel-1,0)) + $e.code[CODE]);
				}
			}
			if($e.code[TYPE]==null || $e.code[TYPE].equals("ERROR"))
			{
				check = "ERROR";
			}
		}
		| e2=expr   
		{
			if(functionCode.size()<nestLevel)//livello appena raggiunto
			{
				if(!check.equals("ERROR"))
				{
					functionCode.add($e2.code[CODE]);
				}
			}
			else
			{
				functionCode.set(Math.max(nestLevel-1,0),functionCode.get(Math.max(nestLevel-1,0)) + $e2.code[CODE]);
			}
			if($e2.code[TYPE]==null || $e2.code[TYPE].equals("ERROR"))
			{
				check = "ERROR";
			}
		}
		)SEMIC)*RETURN expRitorno=expr 
		{
			removePar = "";
			for(int c=1; !check.equals("ERROR") && c<parameterCounter.get(Math.max(nestLevel-1-numIfThenNest,0)); c++) 
			{
				removePar+="\tpop\n";
			}
			if($expRitorno.code[TYPE].equals($ty.text.toUpperCase()) && !check.equals("ERROR") ) 
			{
				$code[TYPE] = $expRitorno.code[TYPE];
				
				if($expRitorno.code[TYPE]!= null && $code[TYPE]!=null && !$expRitorno.code[TYPE].equals("VOID") && !$code[TYPE].equals("ERROR"))
				{
					if(functionCode.size()<nestLevel) //livello appena raggiunto
					{
						functionCode.add(
							$expRitorno.code[CODE] + 
							"\tsrv\n"+
							"\tsal\n" + //qui va bene anche un pop, rimuovo AL dell'AR corrente
							"\tsra\n"+
							removePar+  
							"\tsfp\n"+ //recupero FP del chiamante
							"\tlfp\n"+
							"\tchal\n"+
							"\tsal\n" +
							"\tlrv\n"+
							"\tjra\n\n");
					}
					else
					{
						if(!check.equals("ERROR"))
						{
							functionCode.set(Math.max(nestLevel-1,0),
								functionCode.get(Math.max(nestLevel-1,0)) +
								$expRitorno.code[CODE] + 
									"\tsrv\n"+
									"\tsal\n" + //qui va bene anche un pop, rimuovo AL dell'AR corrente
									"\tsra\n"+
									removePar+  
									"\tsfp\n"+ //recupero FP del chiamante
									"\tlfp\n"+
									"\tchal\n"+
									"\tsal\n" +
									"\tlrv\n"+
									"\tjra\n\n");
						}
					}
				}
				else
				{
					if(functionCode.size() < nestLevel) //livello appena raggiunto
					{
						functionCode.add(
							$expRitorno.code[CODE] + 
							"\tsal\n" +
							"\tsra\n"+
							removePar+  
							"\tsfp\n"+
							"\tjra\n\n");
					}
					else
					{
						functionCode.set(Math.max(nestLevel-1,0),
							functionCode.get(Math.max(nestLevel-1,0)) + 
							$expRitorno.code[CODE] + 
							"\tsal\n" +
							"\tsra\n"+
							removePar+  
							"\tsfp\n"+
							"\tjra\n\n");
					}
				}
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add($i.text + " : valore di ritorno scorretto.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + $i.text + " : valore di ritorno scorretto.\n");
				}
				$code[TYPE] = "ERROR";
			}
		
			$code[CODE]="";
			if(parameterCounter.size()==0 ||  parameterCounter.size() < nestLevel-numIfThenNest)
			{
				parameterCounter.add(1);
			}
			else
			{
				if(!check.equals("ERROR"))
				{
					parameterCounter.set(Math.max(nestLevel-1-numIfThenNest,0),1);
				}
			}
			for(Object ste : symTable.get(nestLevel).entrySet())
			{
				SymTableEntry s = (SymTableEntry)((Map.Entry)ste).getValue();
				if(s.Category()==TRUEVAR)
				{
					staticData--;
				}
			}
			symTable.get(nestLevel).clear();
			symTable.remove(nestLevel);
			nestLevel = Math.max(nestLevel-1,0);
		}
		SEMIC RBPAR
		;
		catch [RecognitionException re] {reportError(re);}
	
command returns [String[\] code]
	@init {
		code = new String[3];
	}
	:
		(PRINT e=expr 
		{
			$code[CODE] = $e.code[CODE];
			if($e.code[TYPE]!=null && !$e.code[TYPE].equals("VOID"))
			{
				if($e.code[TYPE].equals("BOOL"))
				{
					$code[CODE] += "\tprintb\n";
				}
				else
				{
			 		$code[CODE] += "\tprint\n";
			 	}
			}
			if($e.code[TYPE]==null)
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("PRINT : errori non recuperati in precedenza.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "PRINT : errori non recuperati in precedenza.\n");
				}
				$code[TYPE] = "ERROR"; 
			}
			else
			{
				$code[TYPE] = $e.code[TYPE]; 
			}
		}
		| EXEC e=expr 
		{
			$code[CODE] = $e.code[CODE];// + "\tprint\n"; 
			if($e.code[TYPE]==null)
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("CALL : errori non recuperati in precedenza.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "CALL : errori non recuperati in precedenza.\n");
				}
				$code[TYPE] = "ERROR"; 
			}
			else
			{
				$code[TYPE] = $e.code[TYPE]; 
			}
			if($code[TYPE]!=null && !$code[TYPE].equals("VOID"))
			{
				$code[CODE] += "\tpop\n";
			}
		}
		| WHILE  eWhile=expr LBPAR 
		{ 
			numCicli++; 
			nestLevel++; 
			numIfThenNest++; 
			String whileBody = "";  
			symTable.add(new HashMap()); //Operazioni di pulizia sul corrente livello della SymTable 
			symTable.get(nestLevel).clear();
				
			if(!$eWhile.code[TYPE].equals("BOOL"))
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("WHILE : espressione di controllo non booleana.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "WHILE : espressione di controllo non booleana.\n");
				}
				$code[TYPE] = "ERROR";	
			}
			else
			{
				$code[TYPE] = "VOID";	
			}
		} 
		(( cWhile=command 
		{
			whileBody += $cWhile.code[CODE]; 
			if(!$cWhile.code[TYPE].equals("VOID"))
			{
				/*whileBody+="\tpop\n";*/
			}
			if($cWhile.code[TYPE].equals("ERROR"))
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("WHILE : errori non recuperati in precedenza.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "WHILE : errori non recuperati in precedenza.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| eWhile2=expr 
		{
			whileBody += $eWhile2.code[CODE];
			if(!$eWhile2.code[TYPE].equals("VOID"))
			{
				/*whileBody+="\tpop\n";*/
			}
			if($eWhile2.code[TYPE].equals("ERROR"))
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("WHILE : errori non recuperati in precedenza.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "WHILE : errori non recuperati in precedenza.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		)SEMIC)* 
		{
			$code[CODE] =
				"loop" + numCicli + ":\n" +
				$eWhile.code[CODE] +
				"\tpush " + TRUEVALUE + "\n" + 
				"\tbeq true" + numCicli + "\n" +
				"\tb false"+numCicli+"\n"+
				"true"+numCicli+":\n"+
				whileBody +
				"\tb loop" + numCicli + "\n" +
				"false"+numCicli+":\n";
							
			for(Object ste : symTable.get(nestLevel).entrySet()) //Operazioni pulizia Symtable e memoria globale
			{
				SymTableEntry s = (SymTableEntry)((Map.Entry)ste).getValue();
				if(s.Category()==TRUEVAR)
				{
					staticData--;
				}
			}
			symTable.remove(nestLevel);
			nestLevel = Math.max(nestLevel-1,0);
			numIfThenNest = Math.max(numIfThenNest-1,0);		
		}
		RBPAR)
		;
		catch [RecognitionException re] {reportError(re);}

expr returns [String[\] code]
	@init {
		code = new String[3];
	}
	: 
		t1=term 
		{
			$code[CODE] = $t1.code[CODE]; 
			$code[TYPE] = $t1.code[TYPE];
		}
		(PLUS t=term 
		{
			$code[CODE] += $t.code[CODE] + "\tadd\n"; 
			if($t.code[TYPE]!=null && $t1.code[TYPE]!= null && $t.code[TYPE].equals("INT") && $t1.code[TYPE].equals($t.code[TYPE])) 
			{
				$code[TYPE] = "INT";
			} 
			else 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Somma fra termini non validi.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "Somma fra termini non validi.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| MINUS t = term 
		{
			$code[CODE]=$t.code[CODE]+$code[CODE]+"\tsub\n"; 
			if($t.code[TYPE]!=null && $t1.code[TYPE]!= null && $t.code[TYPE].equals("INT") && $t1.code[TYPE].equals($t.code[TYPE]))
			{
				$code[TYPE] = "INT";
			} 
			else 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Sottrazione fra termini non validi.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "Sottrazione fra termini non validi.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| OR t = term 
		{
			$code[CODE] = 
				$code[CODE] +
				"\tpush "+TRUEVALUE+"\n"+
				"\tbeq label"+labelCounter+"\n"+
				$t.code[CODE]+
				"\tpush "+TRUEVALUE+"\n"+
				"\tbeq label"+(labelCounter++)+"\n"+
				"\tpush "+FALSEVALUE+"\n"+
				"\tb label"+(labelCounter++)+"\n"+
				"label"+(labelCounter-2)+":\n"+
				"\tpush "+TRUEVALUE+"\n"+
				"label"+(labelCounter-1)+":\n";
				
			if($t.code[TYPE]!=null && $t1.code[TYPE]!= null && $t.code[TYPE].equals("BOOL") && $t1.code[TYPE].equals($t.code[TYPE])) 
			{
				$code[TYPE] = "BOOL";
			} 
			else 
			{ 				
				if(listoferrors.size()<row)
				{
					listoferrors.add("OR logico fra termini non validi.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "OR logico fra termini non validi.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		)*
		;
		catch [RecognitionException re] {reportError(re);}
	
	
term returns [String[\] code]
	@init {
		code = new String[3];
	}
	: 
		f1=factor 
		{
			$code[CODE] = $f1.code[CODE]; 
			$code[TYPE] = $f1.code[TYPE];
		} 
		(AND f=factor 
		{
			$code[CODE] = 
				$code[CODE]+
				"\tpush "+FALSEVALUE+"\n"+
				"\tbeq label"+labelCounter+"\n"+
				$f.code[CODE]+
				"\tpush "+FALSEVALUE+"\n"+
				"\tbeq label"+(labelCounter++)+"\n"+
				"\tpush "+TRUEVALUE+"\n"+
				"\tb label"+(labelCounter++)+"\n"+
				"label"+(labelCounter-2)+":\n"+
				"\tpush "+FALSEVALUE+"\n"+
				"label"+(labelCounter-1)+":\n";
				
			if($f.code[TYPE]!=null && $f1.code[TYPE]!= null && $f.code[TYPE].equals("BOOL") && $f1.code[TYPE].equals($f.code[TYPE])) 
			{
				$code[TYPE] = "BOOL";
			} 
			else 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("AND logico fra termini non validi.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "AND logico fra termini non validi.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| MUL f=factor 
		{
			$code[CODE] = $code[CODE] + $f.code[CODE] + "\tmul\n"; 
			if($f.code[TYPE]!=null && $f1.code[TYPE]!= null && $f.code[TYPE].equals("INT") && $f1.code[TYPE].equals($f.code[TYPE])) 
			{
				$code[TYPE] = "INT";
			} 
			else 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Moltiplicazione fra termini non validi.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "Moltiplicazione fra termini non validi.\n");
				}
				$code[TYPE]="ERROR";
			}
		}
		)*
		;
		catch [RecognitionException re] {reportError(re);}
	
	
factor returns [String[\] code]
	@init {
		code = new String[3];
	}
	: 
		n=NUMBER 
		{
			$code[CODE] = 	"\tpush " + $n.text+"\n"; 
			$code[TYPE] = "INT";
		}
		| NULL {$code[CODE] = ""; $code[TYPE] = "VOID";}
		| TRUE {$code[CODE] = "\tpush "+TRUEVALUE+"\n"; $code[TYPE] = "BOOL";}
		| FALSE {$code[CODE] = "\tpush "+FALSEVALUE+"\n"; $code[TYPE] = "BOOL";}
		| em=EMPTY {$code[CODE] = "\tpush "+EMPTYVALUE+"\n"; $code[TYPE] = $em.text.equals("emptyint")?"LISTINT":"LISTBOOL";}
		| NOT e=expr 
		{
			$code[CODE] =
				$e.code[CODE]+
				"\tpush "+TRUEVALUE+"\n"+
				"\tbeq label"+(labelCounter++)+"\n"+
				"\tpush "+TRUEVALUE+"\n"+
				"\tb label"+(labelCounter++)+"\n"+
				"label"+(labelCounter-2)+":\n"+
				"\tpush "+FALSEVALUE+"\n"+
				"label"+(labelCounter-1)+":\n";
				
			if($e.code[TYPE]!=null && $e.code[TYPE].equals("BOOL")) 
			{
				$code[TYPE] = "BOOL";
			} 
			else 
			{
			
				if(listoferrors.size()<row)
				{
					listoferrors.add("Negazione di un non booleano.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "Negazione di un non booleano.\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| LSPAR e=expr COMMA f=expr RSPAR 
		{
			$code[CODE] = 
				$f.code[CODE] +
				$e.code[CODE] +
				"\tlhp\n"+
				"\tsw\n"+
				"\tlhp\n"+
				"\tpush 1\n"+
				"\tadd\n"+
				"\tsw\n"+
				"\tlhp\n"+
				"\tlhp\n"+
				"\tpush 2\n"+
				"\tadd\n"+
				"\tshp\n";
				
			if($e.code[TYPE]!=null && $f.code[TYPE]!=null && $e.code[TYPE].equals("INT") && $f.code[TYPE].equals("LISTINT")) 
			{
				$code[TYPE] = "LISTINT";
			} 
			else if($e.code[TYPE]!=null && $f.code[TYPE]!=null && $e.code[TYPE].equals("BOOL") && $f.code[TYPE].equals("LISTBOOL")) 
			{
				$code[TYPE] = "LISTBOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("Costruzione lista con elementi incoerenti.\n");
				}
				else
				{
					listoferrors.set(row-1,listoferrors.get(row-1) + "Costruzione lista con elementi incoerenti.\n");
				}
				$code[TYPE] = "ERROR";
			}      
		}
		| i=ID( 
		{
			SymTableEntry  entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
			int tmpLvl = nestLevel;
			
			while(tmpLvl>0 && entry==null)
			{
				tmpLvl--;
				entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));
            } 
			if (entry == null) 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("La variabile "+$i.text+" non è stata dichiarata.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "La variabile "+$i.text+" non è stata dichiarata.\n");
				}
				$code[TYPE] = "ERROR";
			} 
			else 
			{
				if(entry.category != FUNC && entry.category != LOCFUNC)
				{
					Integer value = (Integer)(entry.Ref());
					if(entry.category==PARAM)
					{
						String ss = "";
						if(tmpLvl==nestLevel-numIfThenNest)
						{
							ss = "\tlfp\n";
						}
						else
						{
							ss = "\tlal\n";
							int dif = nestLevel-numIfThenNest - tmpLvl;
							for(int kk=1;kk<dif;kk++)
							{
								ss += "\tchal\n";
							}
						}
							
						$code[CODE] = 
							ss +
							"\tpush "+value.toString()+"\n"+
							"\tadd\n"+
							"\tlw\n";
					}
					else
					{
						$code[CODE] =
							"\tpush "+value.toString()+"\n"+
							"\tlw\n";
					}
						
					$code[TYPE] = (String)((SymTableEntry)symTable.get(tmpLvl).get($i.text)).Type();
				}
				else
				{					
					if(listoferrors.size()<row)
					{
						listoferrors.add("Si sta cercando di utilizzare la funzione " + $i.text + " come variabile\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + "Si sta cercando di utilizzare la funzione " + $i.text + " come variabile\n");
					}
				
					$code[TYPE] = "ERROR";
				}
			}
		}
		| ASS e=expr 
		{
			SymTableEntry  entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
			int tmpLvl = nestLevel;
            			
			while(tmpLvl>0 && entry==null)
			{
				tmpLvl--;
				entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));	
			} 
			if (entry == null) 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("La variabile " + $i.text + " non è stata definita.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "La variabile " + $i.text + " non è stata definita.\n");
				}
				
				$code[TYPE] = "ERROR";
			} 
			else 
			{
				if(entry.category != FUNC && entry.category != LOCFUNC)
				{
					Integer value = (Integer)(entry.Ref());
					if(entry.category==PARAM)
					{
						String ss = "";
						if(tmpLvl==nestLevel-numIfThenNest)
						{
							ss = "\tlfp\n";
						}
						else
						{
							ss = "\tlal\n";
							int dif = nestLevel-numIfThenNest - tmpLvl;
							for(int kk=1;kk<dif;kk++)
							{
								ss += "\tchal\n";
							}
						}
						
						$code[CODE] = 
							$e.code[CODE] +
							ss +
							"\tpush "+value.toString()+"\n"+
							"\tadd\n"+
							"\tsw\n";
					}
					else
					{
						$code[CODE] = 
							$e.code[CODE] +
							"\tpush "+ value.toString()+ "\n"+
							"\tsw\n";
					}
					
					String typeCorr = (String)((SymTableEntry)symTable.get(tmpLvl).get($i.text)).Type();
					if(!typeCorr.equals($e.code[TYPE]))
					{
					
						if(listoferrors.size()<row)
						{
							listoferrors.add($i.text + ": assegnamento valore di tipo scorretto.\n");
						}
						else
						{
							listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + ": assegnamento valore di tipo scorretto.\n");
						}
						$code[TYPE] = "ERROR";
					}
					else
					{
						$code[TYPE] = $e.code[TYPE];
					}
				}
				else
				{					
					if(listoferrors.size()<row)
					{
						listoferrors.add("Si sta cercando di utilizzare la funzione " + $i.text + " come variabile.\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + "Si sta cercando di utilizzare la funzione " + $i.text + " come variabile.\n");
					}
					
					$code[TYPE] = "ERROR";
				}
			}
		}
		| LPAR 
		{
			$code[CODE] = ""; 
			SymTableEntry  entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
			int tmpLvl = nestLevel;
             			
			while(tmpLvl>0 && entry==null)
			{
				tmpLvl--;
				entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));
			}
             			
			if (entry==null) 
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Funzione " + $i.text + " non dichiarata.\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "Funzione " + $i.text + " non dichiarata.\n");
				}
				
				$code[TYPE] = "ERROR";
			} 
			else 
			{
				if(entry.category!=FUNC && entry.category!=LOCFUNC)
				{					
					if(listoferrors.size()<row)
					{
						listoferrors.add("Si sta cercando di utilizzare la variabile " + $i.text + " come funzione.\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + "Si sta cercando di utilizzare la variabile " + $i.text + " come funzione.\n");
					}
					$code[TYPE] = "ERROR";
				}
				else
				{
					$code[TYPE] = (String)((SymTableEntry)symTable.get(tmpLvl).get($i.text)).Type();
					if(((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList==null || ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.size()==0)
					{
						primoParMancante = false;
					}
					else
					{
						primoParMancante = true;
					}
				}
			}
		}
		(e=expr
		{	
			primoParMancante = false;
			$code[CODE] = $e.code[CODE]; 
			numPar = 0; 
			
			entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
			tmpLvl = nestLevel;
            			
			while(tmpLvl>0 && entry==null)
			{
				tmpLvl--;
				entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));
			}
			
			if(symTable.get(tmpLvl)!= null && (SymTableEntry)symTable.get(tmpLvl).get($i.text)!=null && ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList!=null && ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.size()>numPar)
			{
				String typePar = (String)((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.get(numPar);
               		
				if($e.code[TYPE]==null || !typePar.equals($e.code[TYPE])) 
				{
					if(listoferrors.size()<row)
					{
						listoferrors.add($i.text + " : Parametro 1 di tipo scorretto.\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + " : Parametro 1 di tipo scorretto.\n");
					}
					$code[TYPE] = "ERROR";
				}
				else
				{
					//System.out.println("sono qui qui");
				}
			}
			else
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Troppi parametri per la funzione " + $i.text);
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "Troppi parametri per la funzione " + $i.text);
				}
				$code[TYPE] = "ERROR";
			}
		}
		(COMMA f=expr 
		{
			$code[CODE] = $f.code[CODE]+$code[CODE];
			
			entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
			tmpLvl = nestLevel;
            			
			while(tmpLvl>0 && entry==null)
			{
				tmpLvl--;
				entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));
			}
            			
			numPar++;
			if(((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList!=null && symTable.get(tmpLvl)!= null && ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.size()>numPar)
			{
				String typePar = (String)((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.get(numPar);
			
				if(!typePar.equals($f.code[TYPE])) 
				{
					if(listoferrors.size()<row)
					{
						listoferrors.add($i.text + " : Parametro "+ (numPar+1) + " di tipo scorretto.\n");
					}
					else
					{
						listoferrors.set(row-1, listoferrors.get(row-1) + $i.text + " : Parametro "+ (numPar+1) + " di tipo scorretto.\n");
					}
					$code[TYPE] = "ERROR";
				}
			}
			else
			{				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Troppi parametri per la funzione " + $i.text + ".\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "Troppi parametri per la funzione " + $i.text + ".\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		)*)?RPAR 
		{
			if(primoParMancante==true || (symTable.get(tmpLvl)!= null && symTable.get(tmpLvl).get($i.text)!= null && ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList!=null && ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).paramTypeList.size()>(numPar+1)))
			{
				//System.out.println("Parametri mancanti per la funzione " + $i.text);				
				if(listoferrors.size()<row)
				{
					listoferrors.add("Parametri mancanti per la funzione " + $i.text + ".\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) + "Parametri mancanti per la funzione " + $i.text + ".\n");
				}
				$code[TYPE] = "ERROR";
			}
			else
			{
				String callFunc = "";
				entry = (SymTableEntry)(symTable.get(nestLevel).get($i.text));
				tmpLvl = nestLevel;
            			
				while(tmpLvl>0 && entry==null)
				{
					tmpLvl--;
					entry = (SymTableEntry)(symTable.get(tmpLvl).get($i.text));
				}
           			
           		if(entry!=null)
				{
					int type = ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).Category();
				
					if(type == LOCFUNC)
					{
						callFunc = "\tjal "; //"\tjaln "; //salto a funzione deinita localmente
					}
					else
					{
						callFunc = "\tjal ";
					}
            			
					String setAL = "";
            			
					int newBlockNestLevel = ((SymTableEntry)symTable.get(tmpLvl).get($i.text)).nestLvl;
            			
            		//scelta dell'access link
					if(newBlockNestLevel > nestLevel-numIfThenNest) //sto chiamando una funzione locale
					{
						if(tmpLvl==0)//se è una funzione chiamata dall'ambito globale
						{
							setAL = "\tpush 3\n" +
								"\tlfp\n" +
								"\tsub\n";
						}
						else
						{
							setAL = "\tlfp\n";
						}
					}
					else
					{
						if(newBlockNestLevel==nestLevel-numIfThenNest) //ricorsione o figli dello stesso scope
						{
							setAL = "\tlal\n";
						}
						else //funzione al di fuori dello scope
						{
							//Qui si seguirà la catena di access links
							setAL = "\tlal\n"; //carica AL del blocco chiamante
							int diffProfondita = nestLevel-numIfThenNest-newBlockNestLevel;
							
							for(int ii=0;ii<diffProfondita;ii++)
							{
								setAL += "\tchal\n";
							}
						}
					}
            			
					$code[CODE] = 
						"\tlfp\n" +
						$code[CODE] +
						setAL +
						callFunc +
						"func" + ((SymTableEntry)(symTable.get(tmpLvl).get($i.text))).ID() + $i.text + 
						"\n";
				}
			}
		}
		) | LPAR e=expr (RPAR 
		{
			$code[CODE] = $e.code[CODE]; 
			$code[TYPE] = $e.code[TYPE];
		}
		| EQUAL e2=expr RPAR 
		{
			$code[CODE] = 
				$e2.code[CODE] +
				$e.code[CODE] +
				"\tbeq label" + (labelCounter++) + "\n" +
				"\tpush " + FALSEVALUE + "\n" +
				"\tb label" + (labelCounter++) + "\n" +
				"label" + (labelCounter-2) + ":\n" +
				"\tpush " + TRUEVALUE + "\n" +
				"label" + (labelCounter-1) + ":\n";
				
			if($e.code[TYPE]!=null && $e2.code[TYPE]!=null && !$e.code[TYPE].equals("ERROR") && $e2.code[TYPE].equals($e.code[TYPE])) 
			{
				$code[TYPE] = "BOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("Uguaglianza fra tipi diversi\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"Uguaglianza fra tipi diversi\n");
				}
				$code[TYPE] = "ERROR";
			}
		}
		| LESS e2=expr RPAR 
		{
			$code[CODE] =
				$e2.code[CODE] +
				$e.code[CODE] +
				"\tbless label" + (labelCounter++) + "\n" +
				"\tpush " + FALSEVALUE + "\n" +
				"\tb label" + (labelCounter++) + "\n" +
				"label" + (labelCounter-2) + ":\n" +
				"\tpush " + TRUEVALUE + "\n" +
				"label" + (labelCounter-1) + ":\n";
				
			if($e.code[TYPE]!=null && $e2.code[TYPE]!=null && $e2.code[TYPE].equals("INT") && $e2.code[TYPE].equals($e.code[TYPE])) 
			{
				$code[TYPE] = "BOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("Minore fra tipi non interi\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"Minore fra tipi non interi\n");
				}
				$code[TYPE] = "ERROR";
			}
		}		   
		| GREATER e2=expr RPAR 
		{
			$code[CODE] =
				$e.code[CODE] +
				$e2.code[CODE] +
				"\tbless label" + (labelCounter++) + "\n" +
				"\tpush " + FALSEVALUE + "\n" +
				"\tb label" + (labelCounter++) + "\n" +
				"label" + (labelCounter-2) + ":\n" +
				"\tpush " + TRUEVALUE + "\n" +
				"label" + (labelCounter-1) + ":\n";
				
			if($e.code[TYPE]!=null && $e2.code[TYPE]!=null && $e2.code[TYPE].equals("INT") && $e2.code[TYPE].equals($e.code[TYPE])) 
			{
				$code[TYPE]="BOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("Maggiore fra tipi non interi\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"Maggiore fra tipi non interi\n");
				}
				$code[TYPE] = "ERROR";
			}
		}    
		| DOT(FIRST 
		{
			$code[CODE] = $e.code[CODE] + "\tlw\n"; 
			if ($e.code[TYPE]!=null && $e.code[TYPE].equals("LISTINT")) 
			{
				$code[TYPE] = "INT";
			} 
			else if ($e.code[TYPE]!=null && $e.code[TYPE].equals("LISTBOOL")) 
			{
				$code[TYPE]= "BOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("FIRST su un elemento non stringa\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"FIRST su un elemento non stringa\n");
				}
				$code[TYPE]= "ERROR";
			}
		} 
		| REST 
		{
			$code[CODE] = 
				$e.code[CODE]+
				"\tpush 1"+
				"\tadd\n"+
				"\tlw\n";
				
			if ($e.code[TYPE]!=null && $e.code[TYPE].equals("LISTINT")) 
			{
				$code[TYPE]= "LISTINT";
			} 
			else if ($e.code[TYPE]!=null && $e.code[TYPE].equals("LISTBOOL")) 
			{
				$code[TYPE]= "LISTBOOL";
			} 
			else 
			{
				if(listoferrors.size()<row)
				{
					listoferrors.add("REST su un elemento non stringa\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"RST su un elemento non stringa\n");
				}
				$code[TYPE]= "ERROR";
			}
		}
		)RPAR) | IF e1=expr (THEN)? LBPAR 
		{
			numIfThenNest++; String ifBody = ""; String thenBody = ""; 
			nestLevel++; symTable.add(new HashMap()); symTable.get(nestLevel).clear();
		} 
		((e2=command {ifBody += $e2.code[CODE];}|e4=expr {ifBody += $e4.code[CODE];}) SEMIC)* 
		{
			String type1 = "";
			String type2 = "";
			if($e2.code!=null)
			{
				type1 = $e2.code[TYPE];
			}
			else
			{
				if($e4.code!=null)
				{
					type1 = $e4.code[TYPE];
				}
				else
				{
					type1 = "VOID";
				}
			}
						
						numIfThenNest--;
			
			for(Object ste : symTable.get(nestLevel).entrySet())
			{
				SymTableEntry s = (SymTableEntry)((Map.Entry)ste).getValue();
				if(s.Category()==TRUEVAR)
				{
					staticData--;
				}
			}
			symTable.remove(nestLevel);
			nestLevel = Math.max(nestLevel-1,0);
		}
		RBPAR ELSE LBPAR { numIfThenNest++; nestLevel++; symTable.add(new HashMap()); symTable.get(nestLevel).clear();}((e3=command {thenBody += $e3.code[CODE];}|e5=expr {thenBody += $e5.code[CODE]; }) SEMIC)* 
		RBPAR 
		{
			$code[CODE] = 
				$e1.code[CODE] +
				"\tpush " + TRUEVALUE + "\n" + 
				"\tbeq label" + (labelCounter++) + "\n" +
				thenBody + 
				"\tb label"+(labelCounter++)+"\n"+
				"label"+(labelCounter-2)+":\n"+
				ifBody +
				"label"+(labelCounter-1)+":\n";
							
			ifBody = ""; thenBody = "";
							
			if($e3.code!=null)
			{
				type2 = $e3.code[TYPE];
			}
			else
			{
				if($e5.code!=null)
				{
					type2 = $e5.code[TYPE];
				}
				else
				{
					type2 = "VOID";
				}
			}
			if($e1.code[TYPE]!=null && $e1.code[TYPE].equals("BOOL") && type1.equals(type2)) //i tipi di expr 1 e 2 devono essere coerenti
			{
				$code[TYPE] = type1; 
			}
			else
			{	
				if(listoferrors.size()<row)
				{
					listoferrors.add("Controllo IF non booleano, o discordanza fra tipi dei due nest\n");
				}
				else
				{
					listoferrors.set(row-1, listoferrors.get(row-1) +"Controllo IF non booleano, o discordanza fra tipi dei due nest\n");
				}
				$code[TYPE] = "ERROR";
			} 
			
			for(Object ste : symTable.get(nestLevel).entrySet())
			{
				SymTableEntry s = (SymTableEntry)((Map.Entry)ste).getValue();
				if(s.Category()==TRUEVAR)
				{
					staticData--;
				}
			}
			symTable.remove(nestLevel);
			nestLevel = Math.max(nestLevel-1,0);
			numIfThenNest = Math.max(numIfThenNest-1,0);
		}
		;
		catch [RecognitionException re] {reportError(re);}                      

// LEXER

PLUS    : '+';
MINUS   : '-';
MUL		: '*';	
LPAR    : '(';
RPAR	: ')';
LSPAR   : '[';
RSPAR	: ']';
LBPAR   : '{';
RBPAR	: '}';
SEMIC   : ';';
COMMA   : ',';
DOT		: '.';
DEF     : 'def';
ASS     : '=';
EQUAL	: '==';
LESS	: '<';
GREATER	: '>';
OR		: '||';
AND		: '&&';
NOT		: '!';
PRINT   : 'print';	
IF		: 'if';
THEN	: 'then';
ELSE	: 'else';
TRUE	: 'true';
FALSE	: 'false'; 
EMPTY	: 'emptyint' | 'emptybool';
FIRST	: 'first';
REST	: 'rest';
WHILE	: 'while';
RETURN	: 'return';
EXEC	: 'call' |'exec';
TYP     : 'int' | 'bool' | 'listint' | 'listbool' | 'void';
NULL	: 'null' | 'nil';	
NUMBER  : '0' | (('1'..'9')('0'..'9')*);
ID		: ('a'..'z' | 'A'..'Z')('0'..'9' | 'a'..'z' | 'A'..'Z')*;
WHITESP : ( '\t' | ' ' | '\r' | '\n' )+ { skip(); } ; 
COMMENT : '/*' (options {greedy=false;} : .)* '*/' { skip(); };
ERR		: . { System.out.println("Unrecognized Token");};