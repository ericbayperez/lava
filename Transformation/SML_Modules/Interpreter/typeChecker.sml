(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

exception model_error;

fun typeOf( itree(inode("Expression",_),
                       [ 
                           lor1
                       ]
                   ),
                m0
            ) = typeOf(lor1, m0)

  | typeOf( itree(inode("Lor",_),
               [ 
                    lor1,
                    itree(inode("or",_), [] ),
                    land1
               ]
           ),
        m0
    ) =
    let 
        val t1 = typeOf(lor1, m0)
        val t2 = typeOf(land1, m0) 
    in 
        if t1 = t2 andalso t1 = BOOL then BOOL else ERROR 
    end
    
  | typeOf( itree(inode("Lor",_),
                [
                    land1
                ]
            ),
        m0
    ) = typeOf(land1, m0)
        

| typeOf(  itree(inode("Land",_), 
                [ 
                    land1,
                    itree(inode("and",_), [] ),
                    equals1
                ] 
             ), 
        m0
    ) =
    let 
        val t1 = typeOf(land1, m0)
        val t2 = typeOf(equals1, m0) 
    in 
        if t1 = t2 andalso t1 = BOOL then BOOL
        else ERROR 
    end 

| typeOf(  itree(inode("Land",_), 
                [ 
                    equals1
                ] 
             ), 
        m0
    ) = typeOf(equals1, m0)

| typeOf(  itree(inode("Equals",_), 
                [ 
                    equals1,
                    itree(inode("==",_), [] ),
                    compare1
                ] 
             ), 
        m0
    ) =
    let 
        val t1 = typeOf(equals1, m0)
        val t2 = typeOf(compare1, m0) 
    in 
        if t1 = t2 andalso t1 <> ERROR then BOOL
        else ERROR 
    end
    
  | typeOf(  itree(inode("Equals",_), 
                [ 
                    equals1,
                    itree(inode("!=",_), [] ),
                    compare1
                ] 
             ), 
        m0
    ) =
    let 
        val t1 = typeOf(equals1, m0)
        val t2 = typeOf(compare1, m0) 
    in 
        if t1 = t2 andalso t1 <> ERROR then BOOL
        else ERROR 
    end
  
  | typeOf(  itree(inode("Equals",_), 
                [ 
                    compare1
                ] 
             ), 
        m0
    ) = typeOf(compare1, m0)

| typeOf(  itree(inode("Compare",_), 
                [ 
                    compare1,
                    itree(inode("<",_), [] ),
                    addsub1
                ] 
             ), 
        m0
    ) =
    let 
        val t1 = typeOf(compare1, m0)
        val t2 = typeOf(addsub1, m0) 
    in 
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR 
    end 
    
  | typeOf(  itree(inode("Compare",_), 
                [ 
                    compare1,
                    itree(inode(">",_), [] ),
                    addsub1
                ] 
             ), 
        m0
    ) =
    let 
        val t1 = typeOf(compare1, m0)
        val t2 = typeOf(addsub1, m0) 
    in 
        if t1 = t2 andalso t1 = INT then BOOL
        else ERROR 
    end 

  | typeOf(  itree(inode("Compare",_), 
                [ 
                    addsub1
                ] 
             ), 
        m0
    ) = typeOf(addsub1, m0)

  | typeOf(  itree(inode("AddSub",_), 
                [ 
                    addsub1,
                    itree(inode("+",_), [] ),
                    muldivmo1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(addsub1, m0)
        val t2 = typeOf(muldivmo1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("AddSub",_), 
                [ 
                    addsub1,
                    itree(inode("-",_), [] ),
                    muldivmo1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(addsub1, m0)
        val t2 = typeOf(muldivmo1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("AddSub",_), 
                [ 
                    muldivmo1
                ] 
             ), 
        m0
    ) = typeOf(muldivmo1, m0)

  | typeOf(  itree(inode("MulDivMo",_), 
                [ 
                    muldivmo1,
                    itree(inode("*",_), [] ),
                    negate1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(muldivmo1, m0)
        val t2 = typeOf(negate1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("MulDivMo",_), 
                [ 
                    muldivmo1,
                    itree(inode("/",_), [] ),
                    negate1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(muldivmo1, m0)
        val t2 = typeOf(negate1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("MulDivMo",_), 
                [ 
                    muldivmo1,
                    itree(inode("mod",_), [] ),
                    negate1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(muldivmo1, m0)
        val t2 = typeOf(negate1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("MulDivMo",_), 
                [ 
                    negate1
                ] 
             ), 
        m0
    ) = typeOf(negate1, m0)

| typeOf(  itree(inode("Negate",_), 
                [ 
                    itree(inode("~",_), [] ),
                    negate1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(negate1, m0)
    in
        if t1 = INT then INT
        else ERROR
    end

  | typeOf(  itree(inode("Negate",_), 
                [ 
                    itree(inode("not",_), [] ),
                    negate1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(negate1, m0)
    in
        if t1 = BOOL then BOOL
        else ERROR
    end 

  | typeOf(  itree(inode("Negate",_), 
                [ 
                    exponent1
                ] 
             ), 
        m0
    ) = typeOf(exponent1, m0)

  | typeOf(  itree(inode("Exponent",_), 
                [ 
                    base1,
                    itree(inode("^",_), [] ),
                    exponent1
                ] 
             ), 
        m0
    ) =
    let
        val t1 = typeOf(base1, m0)
        val t2 = typeOf(exponent1, m0)
    in
        if t1 = t2 andalso t1 = INT then INT
        else ERROR
    end
    
  | typeOf(  itree(inode("Exponent",_), 
                [ 
                    base1
                ] 
             ), 
        m0
    ) = typeOf(base1, m0)


  | typeOf(  itree(inode("Base",_),
                [
                  integer1 as itree(inode("Integer",_), children)
                ]
            ),
        m0
    ) = INT
    
    
    | typeOf( itree(inode("Base",_),
                [
                    boolean1 as itree(inode("true",_), children)
                ]
            ),
        m0
    ) = BOOL
            
  | typeOf( itree(inode("Base",_),
                [
                    boolean1 as itree(inode("false",_), children)
                ]
            ),
        m0
    ) = BOOL
        
  | typeOf( itree(inode("Base",_),
                [
                    var1 as itree(inode("Var",_), children)
                ]
            ),
        m0
    ) = getType(accessEnv(getLeaf(var1), m0))

  | typeOf( itree(inode("Base",_),
                [
                    itree(inode("(",_),[]),
                    lor1,
                    itree(inode(")",_),[])
                ]
            ),
        m0
    ) = typeOf(lor1, m0)
    
  | typeOf( itree(inode("Base",_),
                [
                    itree(inode("$",_),[]),
                    lor1,
                    itree(inode("$",_),[])
                ]
            ),
        m0
    ) = typeOf(lor1, m0)
        
  | typeOf( itree(inode("Base",_),
                [
                    increment1
                ]
            ),
        m0
    ) = typeOf(increment1, m0)
     
  | typeOf(itree(inode("Assignment",_),
                [ 
                    var1,
                    itree(inode("=",_), []),
                    expression1
                ]
            ),
        m0
    ) = let
            val t1 = typeOf(expression1, m0)
            val t2 = getType(accessEnv(getLeaf(var1), m0))
        in
            if t1 = t2 then INT
            else raise model_error
        end 
    
  | typeOf(itree(inode("ForChange",_),
                [
                    assignment1 as itree(inode("Assignment",_), children)
                ]
            ),
        m0
    ) = typeOf(assignment1, m0)
    
  | typeOf(itree(inode("ForChange",_),
                [
                    increment1 as itree(inode("Increment",_), children)
                ]
            ),
        m0
    ) = typeOf(increment1, m0)
    
  | typeOf( itree(inode("Increment",_),
                [
                    itree(inode("++",_), []),
                    var1
                ]
            ),
	m0
    ) = let 
            val t = getType(accessEnv(getLeaf(var1), m0)) 
        in
            if t = INT then INT
            else raise model_error
        end

  | typeOf( itree(inode("Increment",_),
                    [
                        var1,
                        itree(inode("++",_), [])
                    ]
		),
            m0
    ) = let 
            val t = getType(accessEnv(getLeaf(var1), m0)) 
        in
            if t = INT then INT
            else raise model_error
        end

  | typeOf( itree(inode("Increment",_),
                [
                    itree(inode("--",_), []),
                    var1
                ]
            ),
        m0
    ) = let 
            val t = getType(accessEnv(getLeaf(var1), m0)) 
        in
            if t = INT then INT
            else raise model_error
        end

  | typeOf( itree(inode("Increment",_),
                [
                    var1,
                    itree(inode("--",_), [])
                ]
            ),
	m0
    ) = let 
            val t = getType(accessEnv(getLeaf(var1), m0)) 
        in
            if t = INT then INT
            else raise model_error
        end
    
  | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")

  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")

  


fun typeCheck( itree(inode("prog",_),
                       [ 
                           stmtList1
                       ]
                   ),
                m0
            ) = typeCheck(stmtList1, m0)
            
  | typeCheck( itree(inode("StatementList",_),
                       [ 
                            stmt1,
                            itree(inode(";",_), [] ),
                            stmtList1
                       ]
                   ),
                m0
            ) = 
            let
                val m1 = typeCheck( stmt1, m0 )
                val m2 = typeCheck( stmtList1, m1 )
            in
                m2
            end
            
  | typeCheck( itree(inode("StatementList",_),
                       [ 
                            epsilon1
                       ]
                   ),
                m0
            ) = m0

| typeCheck( itree(inode("Statement",_),
                       [ 
                            assignment1 as itree(inode("Assignment",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(assignment1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            declaration1 as itree(inode("Declaration",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(declaration1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            block1 as itree(inode("Block",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(block1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            conditional1 as itree(inode("Conditional",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(conditional1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            for1 as itree(inode("For",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(for1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            while1 as itree(inode("While",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(while1, m0)
            
  | typeCheck( itree(inode("Statement",_),
                       [ 
                            print1 as itree(inode("Print",_), children)
                       ]
                   ),
                m0
            ) = typeCheck(print1, m0)

| typeCheck( itree(inode("Declaration",_),
                       [ 
                            itree(inode("int",_), [] ),
                            var1
                       ]
                   ),
                m0
            ) = updateEnv(getLeaf(var1), INT, m0)
            
  | typeCheck( itree(inode("Declaration",_),
                       [ 
                            itree(inode("bool",_), [] ),
                            var1
                       ]
                   ),
                m0
            ) = updateEnv(getLeaf(var1), BOOL, m0)

  | typeCheck( itree(inode("Assignment",_),
                       [ 
                            var1,
                            itree(inode("=",_), [] ),
                            expression1
                       ]
                   ),
                m0
            ) =
            let
                val t1 = typeOf(expression1, m0)
                val t2 = getType(accessEnv(getLeaf(var1), m0))
            in
                if t1 = t2 then m0
                else raise model_error
            end 

  | typeCheck( itree(inode("Conditional",_),
                       [ 
                            itree(inode("if",_), [] ),
                            itree(inode("(",_), [] ),
                            expression1,
                            itree(inode(")",_), [] ),
                            block1
                       ]
                   ),
                m0
            ) =
            let 
                val t = typeOf(expression1, m0) val m1 = typeCheck(block1, m0) 
            in 
                if t = BOOL then m0
                else raise model_error 
            end

  | typeCheck(  itree(inode("Conditional",_), 
                [ 
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    expression1,
                    itree(inode(")",_), [] ),
                    block1,
                    itree(inode("else",_), [] ),
                    block2
                ] 
             ), 
        m0
    ) =
    let 
        val t = typeOf(expression1, m0)
        val m1 = typeCheck(block1, m0)
        val m2 = typeCheck(block2, m0) 
    in 
        if t = BOOL then m0
        else raise model_error 
    end

| typeCheck(  itree(inode("Increment",_), 
                [ 
                    var1,
                    itree(inode("++",_), [])
                ] 
             ), 
        m0
    ) =
    let 
        val t = getType(accessEnv(getLeaf(var1), m0)) 
    in
        if t = INT then m0
        else raise model_error
    end
    
  | typeCheck(  itree(inode("Increment",_), 
                [ 
                    itree(inode("++",_), []),
                    var1
                ] 
             ), 
        m0
    ) =
    let 
        val t = getType(accessEnv(getLeaf(var1), m0)) 
    in
        if t = INT then m0
        else raise model_error
    end
    
  | typeCheck(  itree(inode("Increment",_), 
                [ 
                    itree(inode("--",_), []),
                    var1
                ] 
             ), 
        m0
    ) =
    let 
        val t = getType(accessEnv(getLeaf(var1), m0)) 
    in
        if t = INT then m0
        else raise model_error
    end
    
  | typeCheck(  itree(inode("Increment",_), 
                [ 
                    var1,
                    itree(inode("--",_), [])
                ] 
             ), 
        m0
    ) =
    let 
        val t = getType(accessEnv(getLeaf(var1), m0)) 
    in
        if t = INT then m0
        else raise model_error
    end

  | typeCheck(  itree(inode("While",_), 
                [ 
                    itree(inode("while",_), [] ),
                    itree(inode("(",_), [] ),
                    expression1,
                    itree(inode(")",_), [] ),
                    block1
                ] 
             ), 
        m0
    ) =
    let
        val t = typeOf(expression1, m0)
        val m1 = typeCheck(block1, m0)
    in
        if t = BOOL then m0
        else raise model_error
    end

| typeCheck(  itree(inode("For",_), 
                [ 
                    itree(inode("for",_), [] ),
                    itree(inode("(",_), [] ),
                    assignment1,
                    itree(inode(";",_), [] ),
                    expression1,
                    itree(inode(";",_), [] ),
                    forChange1,
                    itree(inode(")",_), [] ),
                    block1
                ] 
             ), 
        m0
    ) =
    let 
        val m1 = typeCheck( assignment1, m0 )
        val t = typeOf( expression1, m0 )
        val m2 = typeOf( forChange1, m0 )
        val m3 = typeCheck( block1, m0 ) 
    in 
        if t = BOOL then m0
        else raise model_error 
    end

| typeCheck(  itree(inode("Print",_), 
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
        val t = typeOf(expression1, m0)
    in
        if t = ERROR then raise model_error
        else m0
    end

  | typeCheck( itree(inode("Block",_),
                       [ 
                            itree(inode("{",_), [] ),
                            stmtList1,
                            itree(inode("}",_), [] )
                       ]
                   ),
                m0
            ) =
            let
               val (env0, next0, s0) = m0
               val (env1, next1, s1) = typeCheck( stmtList1, m0 )
            in
                (env0, next0, s1)
            end

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








