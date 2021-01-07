------------------------ MODULE TripleDangerSolution ------------------------
EXTENDS Integers
(* --algorithm dragonBlaster
variables energyBursts = 3, executor = "";

process sorcerer = 0
begin
sorcererEnter: while TRUE do
    Monitor1:
        await executor = "";
        executor := "sorcerer";
    SorcererAction:
        energyBursts := energyBursts + 1;
        executor := ""
end while;
end process;

process electicHead = 1
begin
electricHeadEnter: while TRUE do
    A:
        if energyBursts > 0 then
            Monitor2:
                await executor = "";
                executor := "electricHead";
            ElectricHeadAction:    
                energyBursts := energyBursts - 1;      
                executor := "";
        end if;
    B:
        skip;
end while;
end process;

process flameHead = 2
begin
flameHeadEnter: while TRUE do
    C:
        if energyBursts > 0 then
            Monitor3:
                await executor = "";
                executor := "flameHead";
            FlameHeadAction:    
                energyBursts := energyBursts - 1;        
                executor := "";
        end if;
    D:
        skip;
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3c835f8abedb445f9af3928e65d25ac7
VARIABLES energyBursts, executor, pc

vars == << energyBursts, executor, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ energyBursts = 3
        /\ executor = ""
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "sorcererEnter"
                                        [] self = 1 -> "electricHeadEnter"
                                        [] self = 2 -> "flameHeadEnter"]

sorcererEnter == /\ pc[0] = "sorcererEnter"
                 /\ pc' = [pc EXCEPT ![0] = "Monitor1"]
                 /\ UNCHANGED << energyBursts, executor >>

Monitor1 == /\ pc[0] = "Monitor1"
            /\ executor = ""
            /\ executor' = "sorcerer"
            /\ pc' = [pc EXCEPT ![0] = "SorcererAction"]
            /\ UNCHANGED energyBursts

SorcererAction == /\ pc[0] = "SorcererAction"
                  /\ energyBursts' = energyBursts + 1
                  /\ executor' = ""
                  /\ pc' = [pc EXCEPT ![0] = "sorcererEnter"]

sorcerer == sorcererEnter \/ Monitor1 \/ SorcererAction

electricHeadEnter == /\ pc[1] = "electricHeadEnter"
                     /\ pc' = [pc EXCEPT ![1] = "A"]
                     /\ UNCHANGED << energyBursts, executor >>

A == /\ pc[1] = "A"
     /\ IF energyBursts > 0
           THEN /\ pc' = [pc EXCEPT ![1] = "Monitor2"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "B"]
     /\ UNCHANGED << energyBursts, executor >>

Monitor2 == /\ pc[1] = "Monitor2"
            /\ executor = ""
            /\ executor' = "electricHead"
            /\ pc' = [pc EXCEPT ![1] = "ElectricHeadAction"]
            /\ UNCHANGED energyBursts

ElectricHeadAction == /\ pc[1] = "ElectricHeadAction"
                      /\ energyBursts' = energyBursts - 1
                      /\ executor' = ""
                      /\ pc' = [pc EXCEPT ![1] = "B"]

B == /\ pc[1] = "B"
     /\ TRUE
     /\ pc' = [pc EXCEPT ![1] = "electricHeadEnter"]
     /\ UNCHANGED << energyBursts, executor >>

electicHead == electricHeadEnter \/ A \/ Monitor2 \/ ElectricHeadAction
                  \/ B

flameHeadEnter == /\ pc[2] = "flameHeadEnter"
                  /\ pc' = [pc EXCEPT ![2] = "C"]
                  /\ UNCHANGED << energyBursts, executor >>

C == /\ pc[2] = "C"
     /\ IF energyBursts > 0
           THEN /\ pc' = [pc EXCEPT ![2] = "Monitor3"]
           ELSE /\ pc' = [pc EXCEPT ![2] = "D"]
     /\ UNCHANGED << energyBursts, executor >>

Monitor3 == /\ pc[2] = "Monitor3"
            /\ executor = ""
            /\ executor' = "flameHead"
            /\ pc' = [pc EXCEPT ![2] = "FlameHeadAction"]
            /\ UNCHANGED energyBursts

FlameHeadAction == /\ pc[2] = "FlameHeadAction"
                   /\ energyBursts' = energyBursts - 1
                   /\ executor' = ""
                   /\ pc' = [pc EXCEPT ![2] = "D"]

D == /\ pc[2] = "D"
     /\ TRUE
     /\ pc' = [pc EXCEPT ![2] = "flameHeadEnter"]
     /\ UNCHANGED << energyBursts, executor >>

flameHead == flameHeadEnter \/ C \/ Monitor3 \/ FlameHeadAction \/ D

Next == sorcerer \/ electicHead \/ flameHead

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-458ee170f02377d0e1ab77ccde01832d
energyBurstsInvariant == energyBursts >= 0
=============================================================================
\* Modification History
\* Last modified Thu Jan 07 13:27:16 MSK 2021 by Nikitos-U
