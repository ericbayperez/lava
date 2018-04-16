(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)

exception runtime_error;

fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

(*Add functions: accessEnv, accessStore, updateEnv, etc*)

fun error msg = (print msg; raise runtime_error);

fun toInt( Integer x ) = x
    | toInt _ = error "toInt failed";

fun toBool( Boolean false ) = false
    | toBool (Boolean true) = true
    | toBool _ = error "toBoolean failed";
    
fun printFormat( Integer x ) = Int.toString(x)
    | printFormat( Boolean x ) = Bool.toString(x);
    
fun add (Integer x, Integer y) = x + y
    | add _ = error "model.add failed";

fun getLoc (t, loc) = loc;

fun getType (t, loc) = t;

fun accessEnv(id1,(env, next, s))=
    let
        val msg = "Error: accessEnv " ^ id1 ^ "not found.";

        fun aux [] = error msg
            | aux ((id,t,loc)::env) =
                if id1 = id then (t, loc)
                else aux env;
    in 
        aux env
    end;

fun accessStore( loc, (env, next ,s)) =
    let
        val msg = "invalid location : " ^ Int.toString(loc);
    fun aux [] = error msg
        | aux ((loc1,dv1)::s) = 
            if loc1 = loc then dv1 
            else aux s;
    in 
        aux s 
    end;
    
fun updateStore(loc, dv:denotable_value, (env, next, s))=
    let 
        fun aux [] = [(loc, dv)]
            | aux ((loc1, dv1)::s)=
                if loc1 = loc then (loc,dv)::s
                else (loc1, dv1)::aux s;
    in
        (env, next, aux s)
    end;
    
fun updateEnv(id, t, (env,next, s))=
    let
        val msg = "Error: updateEnv " ^ id ^ "already exists. ";
        fun aux [] = [(id,t,next)]
            | aux ((id1,t1,loc1)::env) =
                if id1=id then error msg
                else (id1,t1,loc1)::aux env;
    in
        (aux env, next+1, s)
    end;




(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)






