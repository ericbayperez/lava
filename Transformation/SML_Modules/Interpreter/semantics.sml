(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)


fun E( itree(inode("Expression",_),
                [
                    lor1
                ]
            ),
        m0
    ) = E(lor1, m0)
    
  | E( itree(inode("Lor",_),
                [
                    lor1,
                    itree(inode("or",_),[]),
                    land1
                ]
            ),
        m0
    ) = let
            val(value1, m1) = E(lor1, m0)
        in
            if toBool(value1) then (value1, m1)
            else
                let
                    val(value2, m2) = E(land1, m1)
                in
                    (Boolean(toBool(value2)), m2)
                end
        end
        
  | E( itree(inode("Lor",_),
                [
                    land1
                ]
            ),
        m0
    ) = E(land1, m0)
    
  | E( itree(inode("Land",_),
                [
                    land1,
                    itree(inode("and",_),[]),
                    equals1
                ]
            ),
        m0
    ) = let
            val(value1,m1) = E(land1,m0)
        in
            if toBool(value1) then
                let
                    val(value2,m2) = E(equals1,m1)
                in
                    (Boolean(toBool(value2)),m2)
                end
            else (value1,m1)
        end
        
  | E( itree(inode("Land",_),
                [   
                    equals1
                ]
            ),
        m0
    ) = E(equals1,m0)
    
  | E( itree(inode("Equals",_),
                [
                    equals1,
                    itree(inode("==",_),[]),
                    compare1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(equals1, m0)
            val (value2, m2) = E(compare1, m1)
        in
            (Boolean(value1 = value2), m2)
        end
        
  | E( itree(inode("Equals",_),
                [
                    equals1,
                    itree(inode("!=",_),[]),
                    compare1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(equals1, m0)
            val (value2, m2) = E(compare1, m1)
        in
            (Boolean(value1 <> value2), m2)
        end
                   
  | E( itree(inode("Equals",_),
                [   
                    compare1
                ]
            ),
        m0
    ) = E(compare1,m0)
    
  | E(  itree(inode("Compare",_),
                [
                    compare1,
                    itree(inode("<",_), []),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(value1, m1) = E(compare1, m0)
            val(value2, m2) = E(addsub1, m1)
        in
            (Boolean(toInt(value1) < toInt(value2)),m2)

        end

  | E( itree(inode("Compare",_),
                [
                    compare1,
                    itree(inode(">",_), []),
                    addsub1
                ]
            ),
        m0
    ) = let
            val(value1, m1) = E(compare1, m0)
            val(value2, m2) = E(addsub1, m1)
	in
            (Boolean(toInt(value1) > toInt(value2)), m2)
	end

  | E( itree(inode("Compare",_),
                [
                  addsub1
                ]
            ),
        m0
    ) = E(addsub1, m0)

  | E( itree(inode("AddSub",_),
                [
                    addsub1,
                    itree(inode("+",_), []),
                    muldivmo1
                ]
            ),
        m0
    ) = let
            val(value1,m1) = E(addsub1,m0)
            val(value2,m2) = E(muldivmo1,m1)
            val value3 = Integer(toInt(value1) + toInt(value2))
        in
            (value3, m2)
        end

  | E( itree(inode("AddSub",_),
                [
                    addsub1,
                    itree(inode("-",_), []),
                    muldivmo1
                ]
            ),
         m0
    ) = let
            val(value1,m1) = E(addsub1,m0)
            val(value2,m2) = E(muldivmo1,m1)
            val value3 = Integer(toInt(value1) - toInt(value2))
        in
            (value3, m2)
        end

  | E( itree(inode("AddSub",_),
                [
                    muldivmo1
                ]
            ),
        m0
    ) = E(muldivmo1,m0)
   
  | E( itree(inode("MulDivMo",_),
                [
                    muldivmo1,
                    itree(inode("*",_),[]),
                    negate1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(muldivmo1, m0)
            val (value2, m2) = E(negate1, m1)
            val value3 = Integer(toInt(value1) * toInt(value2))
        in
            (value3, m2)
        end
        
  | E( itree(inode("MulDivMo",_),
                [
                    muldivmo1,
                    itree(inode("/",_),[]),
                    negate1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(muldivmo1, m0)
            val (value2, m2) = E(negate1, m1)
            val value3 = Integer(toInt(value1) div toInt(value2))
        in
            (value3, m2)
        end
        
  | E( itree(inode("MulDivMo",_),
                [
                    muldivmo1,
                    itree(inode("mod",_),[]),
                    negate1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(muldivmo1, m0)
            val (value2, m2) = E(negate1, m1)
            val value3 = Integer(toInt(value1) mod toInt(value2))
        in
            (value3, m2)
        end
   
  | E( itree(inode("MulDivMo",_),
                [
                    negate1
                ]
            ),
        m0
    ) = E(negate1, m0)
        
    | E( itree(inode("Negate",_),
                [
                  itree(inode("~",_), []),
                  negate1
                ]
            ),
        m0
    ) = let
           val(value1,m1) = E(negate1,m0)
           val value2 = toInt(value1)
           val value3 = Integer(~value2)
        in
           (value3,m1)
        end
  
    | E( itree(inode("Negate",_),
                [
                    itree(inode("not",_), []),
                    negate1
                ]
             ),
          m0
    ) = let
            val(value1,m1) = E(negate1,m0)
            val value2 = toBool(value1)
            val value3 = Boolean(not value2)
        in
            (value3, m1)
        end

  | E( itree(inode("Negate",_),
                [
                    exponent1
                ]
              ),
            m0
        ) = E(exponent1,m0)

  | E( itree(inode("Exponent",_),
                [
                    base1,
                    itree(inode("^",_),[]),
                    exponent1
                ]
            ),
        m0
    ) = let
            fun power(a, b) = 
            let
                fun aux(x, i) =
                    if i = b then x
                    else aux(x*a, i+1)
            in
                aux(1,0)
            end
            val (value1, m1) = E(exponent1, m0)
            val (value2, m2) = E(base1, m1)
            val value3 = Integer(power(toInt(value1), toInt(value2)))
        in
            (value3, m2)
        end
   
  | E( itree(inode("Exponent",_),
                [
                    base1
                ]
            ),
        m0
    ) = E(base1, m0)

  | E( itree(inode("Increment",_),
                [
                    itree(inode("++",_), []),
                    var1
                ]
            ),
	m0
    ) = let
		val location = getLoc(accessEnv(getLeaf(var1), m0))
		val value1 = accessStore(location, m0)
                val value2 = add(value1, Integer 1)
		val (m1) = updateStore(location, Integer value2, m0)
	in
		(Integer value2, m1)
	end

  | E( itree(inode("Increment",_),
                    [
                        var1,
                        itree(inode("++",_), [])
                    ]
		),
            m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1), m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer 1)
            val (m1) = updateStore(location, Integer value2, m0)
	in
            (value1, m1)
	end

  | E( itree(inode("Increment",_),
                [
                    itree(inode("--",_), []),
                    var1
                ]
            ),
        m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1), m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer(~1))
            val (m1) = updateStore(location, Integer value2, m0)
	in
            (Integer value2, m1)
	end

  | E( itree(inode("Increment",_),
                [
                    var1,
                    itree(inode("--",_), [])
                ]
            ),
	m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1), m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer(~1))
            val (m1) = updateStore(location, Integer value2, m0)
	in
            (value1, m1)
	end
                 
  | E( itree(inode("Base",_),
                [
                    integer1 as itree(inode("Integer",_), children)
                ]
            ),
        m0
    ) = let
            fun getInt(input) = 
                valOf(Int.fromString input);
            val value1 = getInt(getLeaf(integer1))
        in
            (Integer value1, m0)
        end
   
  | E( itree(inode("Base",_),
                [
                    boolean1 as itree(inode("true",_), children)
                ]
            ),
        m0
    ) = let
            fun getBool(input) = 
                valOf(Bool.fromString input);
            val value1 = getBool(getLeaf(boolean1))
        in
            (Boolean value1, m0)
        end
            
  | E( itree(inode("Base",_),
                [
                    boolean1 as itree(inode("false",_), children)
                ]
            ),
        m0
    ) = let
            fun getBool(input) = 
                valOf(Bool.fromString input);
            val value1 = getBool(getLeaf(boolean1))
        in
            (Boolean value1, m0)
        end
        
  | E( itree(inode("Base",_),
                [
                    var1 as itree(inode("Var",_), children)
                ]
            ),
        m0
    ) = let
            val location = getLoc(accessEnv (getLeaf(var1), m0))
            val value1   = accessStore(location, m0)
        in  
            (value1, m0)
        end

  | E( itree(inode("Base",_),
                [
                    itree(inode("(",_),[]),
                    lor1,
                    itree(inode(")",_),[])
                ]
            ),
        m0
    ) = E(lor1, m0)
    
  | E( itree(inode("Base",_),
                [
                    itree(inode("$",_),[]),
                    lor1,
                    itree(inode("$",_),[])
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(lor1, m0)
            val value2 = toInt(value1)
            fun aux (x) =
                if x < 0 then Integer(x * (~1))
                else Integer(x)
        in	
            (aux(value2), m1)
        end
        
  | E( itree(inode("Base",_),
                [
                    increment1
                ]
            ),
        m0
    ) = E(increment1, m0)

  | E(itree(inode("Assignment",_),
                [ 
                    var1,
                    itree(inode("=",_), []),
                    expression1
                ]
            ),
        m0
    ) = let
            val (value1,m1) = E(expression1, m0)
            val loc = getLoc(accessEnv(getLeaf(var1), m1))
            val m2 = updateStore(loc, value1, m1)
        in
            (value1, m2)
        end
        
  | E(itree(inode("ForChange",_),
                [
                    assignment1 as itree(inode("Assignment",_), children)
                ]
            ),
        m0
    ) = E(assignment1, m0)
    
  | E(itree(inode("ForChange",_),
                [
                    increment1 as itree(inode("Increment",_), children)
                ]
            ),
        m0
    ) = E(increment1, m0)
    

  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.E - this should never occur")
             
fun M(  itree(inode("prog",_), 
                [ 
                    statementlist1
                ] 
             ), 
        m0
    ) = M(statementlist1, m0)
    
 | M(  itree(inode("StatementList",_),
                [
                    statement1,
                    itree(inode(";",_),[]),
                    statementlist1
                ]
            ),
        m0
    ) = let
            val m1 = M(statement1, m0)
            val m2 = M(statementlist1, m1)
        in
            m2
        end
    
  | M(  itree(inode("StatementList",_),
                [
                    epsilon1
                ]
            ),
        m0
    ) = m0
    
  | M(  itree(inode("Statement",_),
                [
                    declaration1 as itree(inode("Declaration",_), children)
                ]
            ),
        m0
    ) = M(declaration1, m0)
    
  | M(  itree(inode("Statement",_),
                [
                    assignment1 as itree(inode("Assignment",_), children)
                ]
            ),
        m0
    ) = M(assignment1, m0)
   
  | M(  itree(inode("Statement",_),
                [
                    conditional1 as itree(inode("Conditional",_), children)
                ]
            ),
        m0
    ) = M(conditional1, m0)
    
  | M(  itree(inode("Statement",_),
                [
                    increment1 as itree(inode("Increment",_), children)
                ]
            ),
        m0
    ) = M(increment1, m0)
  
  | M(  itree(inode("Statement",_),
                [
                    while1 as itree(inode("While",_), children)
                ]
            ),
        m0
    ) = M(while1, m0)
    
  | M(  itree(inode("Statement",_),
                [
                    for1 as itree(inode("For",_), children)
                ]
            ),
        m0
    ) = M(for1, m0)
    
  | M(  itree(inode("Statement",_),
                [
                    print1 as itree(inode("Print",_), children)
                ]
            ),
        m0
    ) = M(print1, m0)
        
    | M(  itree(inode("Statement",_),
                [
                    block1 as itree(inode("Block",_), children)
                ]
            ),
        m0
    ) = M(block1, m0)
    
  | M(  itree(inode("Declaration",_),
                [
                    itree(inode("int",_),[]),
                    var1
                ]
            ),
        m0
    ) = updateEnv(getLeaf(var1), INT, m0)
    
  | M(  itree(inode("Declaration",_),
                [
                    itree(inode("bool",_),[]),
                    var1
                ]
            ),
        m0
    ) = updateEnv(getLeaf(var1), BOOL, m0)
    
  | M(  itree(inode("Assignment",_),
                [
                    var1,
                    itree(inode("=",_), []),
                    expression1
                ]
            ),
        m0
    ) = let
            val (value1,m1) = E(expression1, m0)
            val loc = getLoc(accessEnv(getLeaf(var1), m1))
            val m2 = updateStore(loc, value1, m1)
        in
            m2
        end
        
  | M(  itree(inode("Conditional",_),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    expression1,
                    itree(inode(")",_), []),
                    block1
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(expression1, m0)
        in
            if toBool(value1) then M(block1, m1)
            else m1
        end
   
  | M(  itree(inode("Conditional",_),
                [
                    itree(inode("if",_), []),
                    itree(inode("(",_), []),
                    expression1,
                    itree(inode(")",_), []),
                    block1,
                    itree(inode("else",_), []),
                    block2
                ]
            ),
        m0
    ) = let
            val (value1, m1) = E(expression1, m0)
        in
            if toBool(value1) then M(block1, m1)
            else M(block2, m1)
        end
        
  | M(  itree(inode("While",_),
                [
                    itree(inode("while",_), []),
                    itree(inode("(",_), []),
                    expression1,
                    itree(inode(")",_), []),
                    block1
                ]
            ),
        m0
    ) = let
            fun aux(n0) = 
                let 
                    val (value1, n1) = E(expression1, n0)
                    val n2 = if toBool(value1) then aux(M(block1, n1))
                             else n1
                in
                    n2
                end
        in
            aux(m0)
        end
       
  
  | M( itree(inode("Increment",_),
                [
                    itree(inode("++",_), [] ),
                    var1
                ]
            ),
         m0
    ) = let
           val location = getLoc(accessEnv(getLeaf(var1),m0))
           val value1 = accessStore(location, m0)
           val value2 = add(value1, Integer 1)
           val m1 = updateStore(location,Integer value2, m0)
        in
            m1
        end

  | M( itree(inode("Increment",_),
                  [
                      itree(inode("--",_), [] ),
                      var1
                  ]
               ),
            m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1),m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer ~1)
            val m1 = updateStore(location, Integer value2, m0)
        in
            m1
        end

  | M( itree(inode("Increment",_),
                    [
                        var1,
                        itree(inode("--",_), [] )
                    ]
                ),
             m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1), m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer ~1)
            val m1 = updateStore(location, Integer value2, m0)
        in
            m1
        end

  | M( itree(inode("Increment",_),
                [
                    var1,
                    itree(inode("++",_), [] )
                ]
              ),
          m0
    ) = let
            val location = getLoc(accessEnv(getLeaf(var1), m0))
            val value1 = accessStore(location, m0)
            val value2 = add(value1, Integer 1)
            val m1 = updateStore(location, Integer value2, m0)
        in
            m1
        end

  | M( itree(inode("Block",_),
              [
                  itree(inode("{",_), [] ),
                  statementList1,
                  itree(inode("}",_), [] )
              ]
            ),
        m0
      ) =
      let
          val(env0,next0,s0) = m0
          val(env1,next1,s1) = M( statementList1, m0 )
          val m2 = (env0,next0,s1)
      in
          m2
      end

  | M( itree(inode("Print",_),
              [
                  itree(inode("print",_), [] ),
                  itree(inode("(",_), [] ),
                  expression1,
                  itree(inode(")",_), [] )
              ]
            ),
        m0
     ) =
     let
        val(value1, m1) = E(expression1, m0)
        val str = printFormat(value1)
        val value2 = print(str ^ "\n")
    in
        m1
    end

  | M( itree(inode("For",_),
              [
                  itree(inode("for",_), []),
                  itree(inode("(",_), []),
                  assignment1,
                  itree(inode(";",_), []),
                  expression1,
                  itree(inode(";",_), []),
                  forChange1,
                  itree(inode(")",_), []),
                  block1
              ]
          ),
       m0
    ) = let
            val m1 = M(assignment1, m0)
            val (value1, m2) = E(expression1, m1)
            fun loop(n0)=
                    let
                        val n1 = M(block1, n0)
                        val (value1, n2) = E(forChange1, n1)
                        val (value2, n3) = E(expression1, n2)
                    in
                        if toBool(value2) then loop(n3)
                        else n3
                    end
        in
            if toBool(value1) then loop(m2)
            else m2
        end

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)

