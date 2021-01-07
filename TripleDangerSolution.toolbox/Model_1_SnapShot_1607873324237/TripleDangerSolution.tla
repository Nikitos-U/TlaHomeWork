------------------------ MODULE TripleDangerSolution ------------------------
EXTENDS Integers
(* --algorithm dragonBlaster
variables energyBursts = 3, executor = {};

process sorcerer = 0
begin
    Monitor1:
        await executor = {};
        executor := "sorcerer";
    SorcererAction:
        energyBursts := energyBursts + 1;
        executor := {}
end process;

process electicHead = 1
begin
    A:
        if energyBursts > 0 then
            Monitor2:
                await executor = {};
                executor := "electricHead";
            ElectricHeadAction:    
                energyBursts := energyBursts - 1;      
                executor := {};
        end if;
    B:
        skip;
end process;

process flameHead = 2
begin
    C:
        if energyBursts > 0 then
            Monitor3:
                await executor = {};
                executor := "flameHead";
            FlameHeadAction:    
                energyBursts := energyBursts - 1;        
                executor := {};
        end if;
    D:
        skip;
end process;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e7b50402274fc7b873201125667a10d6
VARIABLES energyBursts, executor, pc

vars == << energyBursts, executor, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ energyBursts = 3
        /\ executor = {}
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Monitor1"
                                        [] self = 1 -> "A"
                                        [] self = 2 -> "C"]

Monitor1 == /\ pc[0] = "Monitor1"
            /\ executor = {}
            /\ executor' = "sorcerer"
            /\ pc' = [pc EXCEPT ![0] = "SorcererAction"]
            /\ UNCHANGED energyBursts

SorcererAction == /\ pc[0] = "SorcererAction"
                  /\ energyBursts' = energyBursts + 1
                  /\ executor' = {}
                  /\ pc' = [pc EXCEPT ![0] = "Done"]

sorcerer == Monitor1 \/ SorcererAction

A == /\ pc[1] = "A"
     /\ IF energyBursts > 0
           THEN /\ pc' = [pc EXCEPT ![1] = "Monitor2"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "B"]
     /\ UNCHANGED << energyBursts, executor >>

Monitor2 == /\ pc[1] = "Monitor2"
            /\ executor = {}
            /\ executor' = "electricHead"
            /\ pc' = [pc EXCEPT ![1] = "ElectricHeadAction"]
            /\ UNCHANGED energyBursts

ElectricHeadAction == /\ pc[1] = "ElectricHeadAction"
                      /\ energyBursts' = energyBursts - 1
                      /\ executor' = {}
                      /\ pc' = [pc EXCEPT ![1] = "B"]

B == /\ pc[1] = "B"
     /\ TRUE
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << energyBursts, executor >>

electicHead == A \/ Monitor2 \/ ElectricHeadAction \/ B

C == /\ pc[2] = "C"
     /\ IF energyBursts > 0
           THEN /\ pc' = [pc EXCEPT ![2] = "Monitor3"]
           ELSE /\ pc' = [pc EXCEPT ![2] = "D"]
     /\ UNCHANGED << energyBursts, executor >>

Monitor3 == /\ pc[2] = "Monitor3"
            /\ executor = {}
            /\ executor' = "flameHead"
            /\ pc' = [pc EXCEPT ![2] = "FlameHeadAction"]
            /\ UNCHANGED energyBursts

FlameHeadAction == /\ pc[2] = "FlameHeadAction"
                   /\ energyBursts' = energyBursts - 1
                   /\ executor' = {}
                   /\ pc' = [pc EXCEPT ![2] = "D"]

D == /\ pc[2] = "D"
     /\ TRUE
     /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << energyBursts, executor >>

flameHead == C \/ Monitor3 \/ FlameHeadAction \/ D

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == sorcerer \/ electicHead \/ flameHead
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b366cd3aad734ac8fd46fbc5caf0a5ff
energyBurstsInvariant == energyBursts >= 0
=============================================================================
\* Modification History
\* Last modified Sun Dec 13 18:28:25 MSK 2020 by a18535673
\* Created Sat Dec 12 17:26:43 MSK 2020 by a18535673
