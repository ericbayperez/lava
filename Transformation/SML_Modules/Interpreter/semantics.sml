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

            
             
            


fun M(  itree(inode("prog",_), 
                [ 
                    stmt_list
                ] 
             ), 
        m
    ) = m
        
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








