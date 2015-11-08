------------------------------- MODULE naive -------------------------------
EXTENDS Integers
CONSTANT N, STOP, EPSILON
ASSUME N \in Nat \ {0,1}
Procs == 1..N
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
(* Hybrid Logical Clocks naive algorithm
--algorithm naive {
    variable pt = [j \in Procs |-> 0],lc = [j \in Procs |-> 0],mailbox= [j \in Procs |-> 0];
    fair process (j \in Procs){  
        J0: while (pt[self] < STOP){ 
                either \* local or receive event
                J1:{ \* phy clocks cannot diverge more than EPSILON
                    await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                    pt[self] := pt[self] + 1;
                    lc[self] := SetMax({lc[self]+1,mailbox[self]+1,pt[self]});
                }
                or \* send event
                J2:{ \* phy clocks cannot diverge more than EPSILON
                    await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                    pt[self] := pt[self] + 1;
                    lc[self] := lc[self] + 1;
                    mailbox[(self%N)+1] :=  lc[self];
                }
            }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES pt, lc, mailbox, pc

vars == << pt, lc, mailbox, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ lc = [j \in Procs |-> 0]
        /\ mailbox = [j \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "J1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "J2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, lc, mailbox >>

J1(self) == /\ pc[self] = "J1"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
            /\ lc' = [lc EXCEPT ![self] = SetMax({lc[self]+1,mailbox[self]+1,pt'[self]})]
            /\ pc' = [pc EXCEPT ![self] = "J0"]
            /\ UNCHANGED mailbox

J2(self) == /\ pc[self] = "J2"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
            /\ lc' = [lc EXCEPT ![self] = lc[self] + 1]
            /\ mailbox' = [mailbox EXCEPT ![(self%N)+1] = lc'[self]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ J1(self) \/ J2(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == (\A k \in Procs: lc[k] >= pt[k])
Sync == (\A k,l \in Procs: pt[k] <= pt[l]+EPSILON)
Bounded == (\A k \in Procs: lc[k] < pt[k] + N*(EPSILON+1))


=============================================================================
\* Modification History
\* Last modified Thu Oct 30 21:00:51 EDT 2014 by Siddharth
\* Created Thu Oct 30 08:26:40 EDT 2014 by Siddharth

For the model with:
    EPSILON=3
    N=3
    STOP=20

We see that the property, 
    Bounded == (\A k \in Procs: lc[k] < pt[k] + N*(EPSILON+1))
Get's violated on running the model check. 

An instance of the counter example obtained by TLA+ model checker is given below:

Starting with Initial predicate:
Since there exist three process, the physical times are <0,0,0> for Process 1, 
Process 2 and Process 3 respectively.
Similarly, the Logical times are <0,0,0>.

We see that for the bound gets violated after 33 states for the given instance:
PT = <6,4,6>
LC = <15,16,12>

We see that for Process 2, 
LC=16 is not less than the bound, 16 ((PT + N*(EPSILON+1)=(4+3*(3+1)))
{LC<PT+N*(EPSILON+1) results to FALSE}

   [0,0]                                      [6,15]    
P1 -------------------------------------------------------
   [0,0]                                           [4,16]
P2 -------------------------------------------------------
   [0,0]                                 [6,12]
P3 -------------------------------------------------------

Hence the bound gets violated in the naive algorithm implementation of Hybrid Logical Clocks. 

This proves that 'l-pt' diverges as we continue the message loop. 
-------------------------------------------------------------------------------
Project submitted by Siddharth Krishna Sinha (ssinha4@buffalo.edu)
-------------------------------------------------------------------------------
