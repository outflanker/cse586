------------------------------- MODULE beans -------------------------------
EXTENDS Integers
CONSTANTS R, G, B
ASSUME /\ R \in 1..100
       /\ G \in 1..100
       /\ B \in 1..100
       /\ R+G+B > 0
(*
--fair algorithm beans {
   variable r=R, g=G, b=B;
  {S:while (TRUE)
     { either 
A1r:    {await (r>1); \* same color and red
           r:=r-2; g:=g+1; b:=b+1;
          };
       or
A1g:    {await (g>1); \* same color and green
          g:=g-2; r:=r+1; b:=b+1;
         };            
       or
A1b:    {await (b>1); \* same color and blue
          b:=b-2; r:=r+1; g:=g+1;
         };            
       or
A2rg:   {await (r>0 /\ g>0); \* different color red and green
          r:=r-1; g:=g-1; b:=b+1;
         };  
       or
A2bg:   {await (b>0 /\ g>0); \* different color blue and green
          b:=b-1; g:=g-1; r:=r+1;
         };  
       or
A2rb:   {await (r>0 /\ b>0); \* different color red and blue
          r:=r-1; b:=b-1; g:=g+1;
         };            
      }\* end while
    }\* end alg
   }\* end alg
*)
\* BEGIN TRANSLATION
VARIABLES r, g, b, pc

vars == << r, g, b, pc >>

Init == (* Global variables *)
        /\ r = R
        /\ g = G
        /\ b = B
        /\ pc = "S"

S == /\ pc = "S"
     /\ \/ /\ pc' = "A1r"
        \/ /\ pc' = "A1g"
        \/ /\ pc' = "A1b"
        \/ /\ pc' = "A2rg"
        \/ /\ pc' = "A2bg"
        \/ /\ pc' = "A2rb"
     /\ UNCHANGED << r, g, b >>

A1r == /\ pc = "A1r"
       /\ (r>1)
       /\ r' = r-2
       /\ g' = g+1
       /\ b' = b+1
       /\ pc' = "S"

A1g == /\ pc = "A1g"
       /\ (g>1)
       /\ g' = g-2
       /\ r' = r+1
       /\ b' = b+1
       /\ pc' = "S"

A1b == /\ pc = "A1b"
       /\ (b>1)
       /\ b' = b-2
       /\ r' = r+1
       /\ g' = g+1
       /\ pc' = "S"

A2rg == /\ pc = "A2rg"
        /\ (r>0 /\ g>0)
        /\ r' = r-1
        /\ g' = g-1
        /\ b' = b+1
        /\ pc' = "S"

A2bg == /\ pc = "A2bg"
        /\ (b>0 /\ g>0)
        /\ b' = b-1
        /\ g' = g-1
        /\ r' = r+1
        /\ pc' = "S"

A2rb == /\ pc = "A2rb"
        /\ (r>0 /\ b>0)
        /\ r' = r-1
        /\ b' = b-1
        /\ g' = g+1
        /\ pc' = "S"

Next == S \/ A1r \/ A1g \/ A1b \/ A2rg \/ A2bg \/ A2rb

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION
TypeOK == /\ r \in 0..200
          /\ g \in 0..200
          /\ b \in 0..200
Termination == <> ((r+g+b) < 2)

=============================================================================
\* Modification History
\* Last modified Tue Sep 30 22:18:41 EDT 2014 by Siddharth
\* Created Tue Sep 23 21:57:48 EDT 2014 by Siddharth

The invariant functions are given as:
1. (r+g+b) > 0
2. r >= 0
3. g >= 0
4. b >= 0

The above are verified my model checking. The first invariant is however given
as (r+g+b) > 1 in the model to avoid stuttering. 
When the invariant is violated we know that the program has reached a fixed point.
-----------------------------------------------------------------------------
The metric/variant function can be given as the total number of beans:
 
  No.B = (r+g+b) is the metric function. 
  
We observe from the program that the No.B either stays the same or 
decreases for each action and hence selected as the metric funtion.
-----------------------------------------------------------------------------
Fixed point:

To find the FP, we take the guards and negate it to get:

 r < 2
^g < 2
^b < 2
^(r < 1) v (g < 1)
^(b < 1) v (g < 1)
^(r < 1) v (b < 1)

But we know that atleast one of them should be '1' from the invariant (r+g+b)>0. 

Therefore the fixed points states are given as (<r>,<g>,<b>) :
1. <1,0,0>
2. <0,1,0>
3. <0,0,1>

We also know that the program terminates when (r+g+b)< 2, or more specifically 
when r+b+g=1.(This can be verified using TLA+ model checking).
This is also given by the metric function No.B(r+g+b) the value of which either 
decreases or stays the same after every action. 
-------------------------------------------------------------------------------
Project submitted by Siddharth Krishna Sinha (ssinha4@buffalo.edu)
-------------------------------------------------------------------------------
