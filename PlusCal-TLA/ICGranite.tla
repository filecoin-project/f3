(* Implements 2 rounds (round=0 and round=1) of Granite *)
(* This version omits the check for external, post-invocation, ECcompatible values and always sways in CONVERGE step*)
--------------------------- MODULE ICGranite ---------------------------

EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANT N, PT, Input, Bottom
\* Put number of nodes/participants in N, and in PT, a sequence of their integer powers, e.g., 
\* N=4, PT = <<1,1,1,1>> for equal weights
\* Input is a sequence of input canonical chains, with empty sequence as a base chain, e.g., 
\* Input = << <<"a">>, <<"b">>, <<"a","c">>, <<"a", "c", "d">> >>
\* Bottom = <<"bottom">>

ASSUME N\in Nat /\ Len(PT)=N /\ Len(Input) = N

RECURSIVE SeqSum(_), isPrefix(_,_), Seq2PrefixSet(_), AllPrefixes(_) 

Tickets == 1..N

SeqSum(s) == IF s = <<>> THEN 0 ELSE
   Head(s) + SeqSum(Tail(s))

isPrefix(a,b) == IF Len(a)>Len(b) THEN FALSE ELSE 
                    IF a = <<>> THEN TRUE ELSE 
                        IF Head(a)#Head(b) THEN FALSE ELSE 
                            isPrefix(Tail(a),Tail(b))

Seq2PrefixSet(s) == IF s = <<>> THEN {<<>>} ELSE 
            IF Len(s) = 1 THEN {<<>>,s} ELSE 
            {s} \union Seq2PrefixSet(SubSeq(s, 1, Len(s)-1))

AllPrefixes(input) == IF input = <<>> THEN {} ELSE
            Seq2PrefixSet(Head(input)) \union AllPrefixes(Tail(input))

AllInputPrefixes == AllPrefixes(Input)

66percQAP == (2*SeqSum(PT)) \div 3

HeaviestChain(S) == IF S={} THEN <<>> ELSE CHOOSE c \in S: \A d \in S: Len(c)>=Len(d) 

SP == 1..N


(*--algorithm ICGranite {
  variables SentMsgs={}; \* Models a broadcast network
  tickets = 1..N; decisions = {}; decided = [sp \in SP |-> FALSE] \*TODO this works only for 1 round of tickets, expand to more
  
  define {
    \* quality related
    SentTypedMsgs(t) == {m \in SentMsgs: (m.type=t)}
    RECURSIVE PrefixPower(_,_)
    PrefixPower(prefix,msgset) == IF msgset={} THEN 0 ELSE
        LET msg == CHOOSE msg \in msgset: TRUE 
            IN IF isPrefix(prefix,msg.value) THEN PT[msg.id] + PrefixPower(prefix,msgset\{msg}) ELSE 
             PrefixPower(prefix,msgset\{msg})
    StrongQuorum(prefix,M) == PrefixPower(prefix,M) > 66percQAP
    \* prepare and commit related
    SentTypedRoundMsgs(t,r) == {m \in SentMsgs: (m.type=t) /\ (m.round=r)}
    RECURSIVE PowerMsgSet(_)
    PowerMsgSet(msgset) == IF msgset={} THEN 0 ELSE
        LET msg == CHOOSE msg \in msgset: TRUE 
           IN  PT[msg.id] + PowerMsgSet(msgset\{msg})
    Power(t,r)==PowerMsgSet(SentTypedRoundMsgs(t,r)) 
    RECURSIVE ProposalsInMsgSet(_)
    ProposalsInMsgSet(proposeset) == IF proposeset = {} THEN {} ELSE 
        LET msg == CHOOSE msg \in proposeset:TRUE 
        IN {msg.value} \union ProposalsInMsgSet(proposeset\{msg})
    RECURSIVE PropWeight(_,_)
    PropWeight(prop,msgset) == IF msgset = {} THEN 0 ELSE 
        LET msg == CHOOSE msg \in msgset: TRUE
        IN  IF msg.value = prop THEN PT[msg.id] + PropWeight(prop,msgset\{msg}) ELSE 
        PropWeight(prop,msgset\{msg})
    HasStrongQuorum(msgset) == \E v \in ProposalsInMsgSet(msgset): PropWeight(v,msgset) > 66percQAP
    StrongQuorumValue(msgset) == CHOOSE v\in ProposalsInMsgSet(msgset): PropWeight(v,msgset) > 66percQAP  
    
    \* converge related 
    RECURSIVE Mintkt(_) \* minimum ticket in a set
    Mintkt(M) == IF M = {} THEN N+1 ELSE 
    LET msg == CHOOSE msg \in M: TRUE
        IN IF msg.ticket < Mintkt(M\{msg}) THEN msg.ticket ELSE Mintkt(M\{msg})
    LowestTicketProposal(M) == IF M = {} THEN {<<>>} ELSE 
        CHOOSE prop \in ProposalsInMsgSet(M): 
            \E msg \in M: (msg.ticket = Mintkt(M)) /\ (msg.value = prop)
  }
  
  \* \* participant calls this to send QUAL msg to peers
   macro sendQUAL() 
   {
     SentMsgs:=SentMsgs \union {[id|-> self, type |->"QUAL", value |-> proposal]};
   }
   
   \* sends PREPARE 
   macro sendPREP()
   {
     if (round = 0) {  \* PREPARE in round 0
       C := {prefix \in Seq2PrefixSet(proposal): StrongQuorum(prefix,SentTypedMsgs("QUAL"))};
       if (C={}) 
            proposal := <<>>;
       else 
            proposal := HeaviestChain(C);
       value:=proposal;
     } else {          \* PREPARE in round >0
     \* await (Power("CONV",round)>66percQAP);
     value := LowestTicketProposal(SentTypedRoundMsgs("CONV",round));  
     \* Here we miss line 26 check and sway directly (as a simplification)
     proposal := value; 
     };
     SentMsgs:=SentMsgs \union {[id|-> self, type |->"PREP", value |-> value, round |-> round]};
   }
   
   \* sends COMMIT 
   macro sendCOMM()
   {
     await (Power("PREP",round)>66percQAP \/ decided[self]=TRUE);
     if (~decided[self]) {
     if (HasStrongQuorum(SentTypedRoundMsgs("PREP",round)) /\ StrongQuorumValue(SentTypedRoundMsgs("PREP",round)) = proposal)  
        value:= proposal; 
     else {
        C := {prefix \in Seq2PrefixSet(proposal): StrongQuorum(prefix,SentTypedRoundMsgs("PREP",round))};
        proposal := HeaviestChain(C); 
        value:=Bottom;
     };
     SentMsgs:=SentMsgs \union {[id|-> self, type |->"COMM", value |-> value, round |-> round]};
     }
   }
   
   \*Decide or next round
   macro processCOMMIT()
   {
     await (Power("COMM",round)>66percQAP \/ decided[self]=TRUE);
     if (~decided[self]) {
     if (HasStrongQuorum(SentTypedRoundMsgs("COMM",round)) /\ StrongQuorumValue(SentTypedRoundMsgs("COMM",round)) # Bottom) {
            decisions := decisions \union {StrongQuorumValue(SentTypedRoundMsgs("COMM",round))};
            decided[self] := TRUE;
            assert (Cardinality(decisions) = 1) \* only one element in decisions always (Agreement)
     } else { 
       if (Cardinality(ProposalsInMsgSet(SentTypedRoundMsgs("COMM",round)))>1) {
          proposal := CHOOSE v \in ProposalsInMsgSet(SentTypedRoundMsgs("COMM",round)): v#Bottom;
       };
         assert (Cardinality(decisions)>0)=>(Cardinality(decisions)=1 /\ \E d\in decisions: d=proposal);
     }; 
     round:=round+1;
     }
   }
   
   \* sends CONVERGE (round>0)
   macro sendCONV() 
   {
        with (t \in tickets) { \* this plays VRF, at least in round=1, assigns random tickets to processes
            tkt :=t;
            tickets := tickets \ {tkt};
        };
        SentMsgs:=SentMsgs \union {[id|-> self, type |->"CONV", value |-> proposal, round|-> round, ticket |-> tkt]};
        assert tkt \in Tickets;
   }
   
   macro sendDecide() {
        if (decided[self]) decided := [sp\in SP |-> TRUE]; 
   }
    
  fair process (name \in SP) 
  variables proposal = Input[self]; round = 0; tkt=0; value = Input[self]; C={};
 {
 l: while(~decided[self] /\ round < 2) {   \*TODO change round to be param 
     if (round = 0) 
        SendQUAL: sendQUAL();
     else {
        SendCONV: sendCONV();
     };
     SendPREP: sendPREP();
     SendCOMM: sendCOMM();
     ProcessCommit: processCOMMIT();
  };
     SendDecide: sendDecide();  
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a47cb318" /\ chksum(tla) = "34b231db")
VARIABLES SentMsgs, tickets, decisions, decided, pc

(* define statement *)
SentTypedMsgs(t) == {m \in SentMsgs: (m.type=t)}
RECURSIVE PrefixPower(_,_)
PrefixPower(prefix,msgset) == IF msgset={} THEN 0 ELSE
    LET msg == CHOOSE msg \in msgset: TRUE
        IN IF isPrefix(prefix,msg.value) THEN PT[msg.id] + PrefixPower(prefix,msgset\{msg}) ELSE
         PrefixPower(prefix,msgset\{msg})
StrongQuorum(prefix,M) == PrefixPower(prefix,M) > 66percQAP

SentTypedRoundMsgs(t,r) == {m \in SentMsgs: (m.type=t) /\ (m.round=r)}
RECURSIVE PowerMsgSet(_)
PowerMsgSet(msgset) == IF msgset={} THEN 0 ELSE
    LET msg == CHOOSE msg \in msgset: TRUE
       IN  PT[msg.id] + PowerMsgSet(msgset\{msg})
Power(t,r)==PowerMsgSet(SentTypedRoundMsgs(t,r))
RECURSIVE ProposalsInMsgSet(_)
ProposalsInMsgSet(proposeset) == IF proposeset = {} THEN {} ELSE
    LET msg == CHOOSE msg \in proposeset:TRUE
    IN {msg.value} \union ProposalsInMsgSet(proposeset\{msg})
RECURSIVE PropWeight(_,_)
PropWeight(prop,msgset) == IF msgset = {} THEN 0 ELSE
    LET msg == CHOOSE msg \in msgset: TRUE
    IN  IF msg.value = prop THEN PT[msg.id] + PropWeight(prop,msgset\{msg}) ELSE
    PropWeight(prop,msgset\{msg})
HasStrongQuorum(msgset) == \E v \in ProposalsInMsgSet(msgset): PropWeight(v,msgset) > 66percQAP
StrongQuorumValue(msgset) == CHOOSE v\in ProposalsInMsgSet(msgset): PropWeight(v,msgset) > 66percQAP


RECURSIVE Mintkt(_)
Mintkt(M) == IF M = {} THEN N+1 ELSE
LET msg == CHOOSE msg \in M: TRUE
    IN IF msg.ticket < Mintkt(M\{msg}) THEN msg.ticket ELSE Mintkt(M\{msg})
LowestTicketProposal(M) == IF M = {} THEN {<<>>} ELSE
    CHOOSE prop \in ProposalsInMsgSet(M):
        \E msg \in M: (msg.ticket = Mintkt(M)) /\ (msg.value = prop)

VARIABLES proposal, round, tkt, value, C

vars == << SentMsgs, tickets, decisions, decided, pc, proposal, round, tkt, 
           value, C >>

ProcSet == (SP)

Init == (* Global variables *)
        /\ SentMsgs = {}
        /\ tickets = 1..N
        /\ decisions = {}
        /\ decided = [sp \in SP |-> FALSE]
        (* Process name *)
        /\ proposal = [self \in SP |-> Input[self]]
        /\ round = [self \in SP |-> 0]
        /\ tkt = [self \in SP |-> 0]
        /\ value = [self \in SP |-> Input[self]]
        /\ C = [self \in SP |-> {}]
        /\ pc = [self \in ProcSet |-> "l"]

l(self) == /\ pc[self] = "l"
           /\ IF ~decided[self] /\ round[self] < 2
                 THEN /\ IF round[self] = 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "SendQUAL"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "SendCONV"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "SendDecide"]
           /\ UNCHANGED << SentMsgs, tickets, decisions, decided, proposal, 
                           round, tkt, value, C >>

SendPREP(self) == /\ pc[self] = "SendPREP"
                  /\ IF round[self] = 0
                        THEN /\ C' = [C EXCEPT ![self] = {prefix \in Seq2PrefixSet(proposal[self]): StrongQuorum(prefix,SentTypedMsgs("QUAL"))}]
                             /\ IF C'[self]={}
                                   THEN /\ proposal' = [proposal EXCEPT ![self] = <<>>]
                                   ELSE /\ proposal' = [proposal EXCEPT ![self] = HeaviestChain(C'[self])]
                             /\ value' = [value EXCEPT ![self] = proposal'[self]]
                        ELSE /\ value' = [value EXCEPT ![self] = LowestTicketProposal(SentTypedRoundMsgs("CONV",round[self]))]
                             /\ proposal' = [proposal EXCEPT ![self] = value'[self]]
                             /\ C' = C
                  /\ SentMsgs' = (SentMsgs \union {[id|-> self, type |->"PREP", value |-> value'[self], round |-> round[self]]})
                  /\ pc' = [pc EXCEPT ![self] = "SendCOMM"]
                  /\ UNCHANGED << tickets, decisions, decided, round, tkt >>

SendCOMM(self) == /\ pc[self] = "SendCOMM"
                  /\ (Power("PREP",round[self])>66percQAP \/ decided[self]=TRUE)
                  /\ IF ~decided[self]
                        THEN /\ IF HasStrongQuorum(SentTypedRoundMsgs("PREP",round[self])) /\ StrongQuorumValue(SentTypedRoundMsgs("PREP",round[self])) = proposal[self]
                                   THEN /\ value' = [value EXCEPT ![self] = proposal[self]]
                                        /\ UNCHANGED << proposal, C >>
                                   ELSE /\ C' = [C EXCEPT ![self] = {prefix \in Seq2PrefixSet(proposal[self]): StrongQuorum(prefix,SentTypedRoundMsgs("PREP",round[self]))}]
                                        /\ proposal' = [proposal EXCEPT ![self] = HeaviestChain(C'[self])]
                                        /\ value' = [value EXCEPT ![self] = Bottom]
                             /\ SentMsgs' = (SentMsgs \union {[id|-> self, type |->"COMM", value |-> value'[self], round |-> round[self]]})
                        ELSE /\ TRUE
                             /\ UNCHANGED << SentMsgs, proposal, value, C >>
                  /\ pc' = [pc EXCEPT ![self] = "ProcessCommit"]
                  /\ UNCHANGED << tickets, decisions, decided, round, tkt >>

ProcessCommit(self) == /\ pc[self] = "ProcessCommit"
                       /\ (Power("COMM",round[self])>66percQAP \/ decided[self]=TRUE)
                       /\ IF ~decided[self]
                             THEN /\ IF HasStrongQuorum(SentTypedRoundMsgs("COMM",round[self])) /\ StrongQuorumValue(SentTypedRoundMsgs("COMM",round[self])) # Bottom
                                        THEN /\ decisions' = (decisions \union {StrongQuorumValue(SentTypedRoundMsgs("COMM",round[self]))})
                                             /\ decided' = [decided EXCEPT ![self] = TRUE]
                                             /\ Assert((Cardinality(decisions') = 1), 
                                                       "Failure of assertion at line 135, column 13 of macro called at line 172, column 21.")
                                             /\ UNCHANGED proposal
                                        ELSE /\ IF Cardinality(ProposalsInMsgSet(SentTypedRoundMsgs("COMM",round[self])))>1
                                                   THEN /\ proposal' = [proposal EXCEPT ![self] = CHOOSE v \in ProposalsInMsgSet(SentTypedRoundMsgs("COMM",round[self])): v#Bottom]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED proposal
                                             /\ Assert((Cardinality(decisions)>0)=>(Cardinality(decisions)=1 /\ \E d\in decisions: d=proposal'[self]), 
                                                       "Failure of assertion at line 140, column 10 of macro called at line 172, column 21.")
                                             /\ UNCHANGED << decisions, 
                                                             decided >>
                                  /\ round' = [round EXCEPT ![self] = round[self]+1]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << decisions, decided, proposal, 
                                                  round >>
                       /\ pc' = [pc EXCEPT ![self] = "l"]
                       /\ UNCHANGED << SentMsgs, tickets, tkt, value, C >>

SendQUAL(self) == /\ pc[self] = "SendQUAL"
                  /\ SentMsgs' = (SentMsgs \union {[id|-> self, type |->"QUAL", value |-> proposal[self]]})
                  /\ pc' = [pc EXCEPT ![self] = "SendPREP"]
                  /\ UNCHANGED << tickets, decisions, decided, proposal, round, 
                                  tkt, value, C >>

SendCONV(self) == /\ pc[self] = "SendCONV"
                  /\ \E t \in tickets:
                       /\ tkt' = [tkt EXCEPT ![self] = t]
                       /\ tickets' = tickets \ {tkt'[self]}
                  /\ SentMsgs' = (SentMsgs \union {[id|-> self, type |->"CONV", value |-> proposal[self], round|-> round[self], ticket |-> tkt'[self]]})
                  /\ Assert(tkt'[self] \in Tickets, 
                            "Failure of assertion at line 154, column 9 of macro called at line 168, column 19.")
                  /\ pc' = [pc EXCEPT ![self] = "SendPREP"]
                  /\ UNCHANGED << decisions, decided, proposal, round, value, 
                                  C >>

SendDecide(self) == /\ pc[self] = "SendDecide"
                    /\ IF decided[self]
                          THEN /\ decided' = [sp\in SP |-> TRUE]
                          ELSE /\ TRUE
                               /\ UNCHANGED decided
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << SentMsgs, tickets, decisions, proposal, 
                                    round, tkt, value, C >>

name(self) == l(self) \/ SendPREP(self) \/ SendCOMM(self)
                 \/ ProcessCommit(self) \/ SendQUAL(self) \/ SendCONV(self)
                 \/ SendDecide(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in SP: name(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SP : WF_vars(name(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Nov 20 17:36:38 CET 2023 by marko
\* Created Thu Nov 02 17:53:45 CET 2023 by marko
