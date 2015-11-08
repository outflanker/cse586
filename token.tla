------------------------------- MODULE token -------------------------------
EXTENDS Integers
CONSTANTS N, M
(* Dijkstra's stabilizing token ring algorithm
--fair algorithm StabTokenRing {
    variable token = [j \in 0..N |-> (j%M)];
    { while (TRUE)
        { either with (j \in 1..N)
            { await (token[j] /= token[(j-1)]);
                token[j] := token[(j-1)];
            }
          or 
            { await (token[0] = token[N]);
                token[0] := (token[N] + 1)%M;
            }
        }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLE token

vars == << token >>

Init == (* Global variables *)
        /\ token = [j \in 0..N |-> (j%M)]

Next == \/ /\ \E j \in 1..N:
                /\ (token[j] /= token[(j-1)])
                /\ token' = [token EXCEPT ![j] = token[(j-1)]]
        \/ /\ (token[0] = token[N])
           /\ token' = [token EXCEPT ![0] = (token[N] + 1)%M]

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION
InvProp ==  /\(\A k \in 1..N: token[k] <= token[(k-1)])
            /\(\A k,l \in 0..N: (token[k] - token[l])<=1)
Stabilization== <> InvProp
=============================================================================
\* Modification History
\* Last modified Sun Dec 14 22:56:54 EST 2014 by Siddharth
\* Created Fri Dec 12 03:29:12 EST 2014 by Siddharth

CounterExample:
ProcessStates = (0 :> 1) (1 :> 1) (2 :> 0) (3 :> 1) (4 :> 0)

In the above example we see that there exist two tokens:
Process 2 contains 1 token and Process 4 contains the other. This is in violation of the 
invariant. 

Invariant: The invariant states that there exist a one and only token in the ring system.
-------------------------------------------------------------------------------
Project submitted by Siddharth Krishna Sinha (ssinha4@buffalo.edu)
-------------------------------------------------------------------------------
