----------------------------- MODULE ringbuffer -----------------------------



\* Modification History
\* Last modified Wed Dec 13 23:27:42 GMT 2023 by samue
\* Created Sat Dec 09 14:08:07 GMT 2023 by samue

EXTENDS Integers, TLC, Sequences

CONSTANTS
    \* Number of philosophers
    NThreads,
    assigned,
    size
    
ASSUME
    /\ NThreads \in Nat \ {0}

\* Choose something to represent the absence of a value. *.


sizeN == size - 1

ASSUME
    /\ NThreads \in Nat \ {0}

(* --algorithm RingBuffer

variables

    sent = [thread \in 1..size |-> [
               Writer |-> "not-written",
               Reader |-> "not-read"
        ]
      ];
    types = {"reader", "writer"};
    
    
    threads = [
        thread \in 1..NThreads |-> [
        \* We create a thread proportion according to the assigned list
            type |-> assigned[thread],
            start |-> 1,
            endr |-> 1,
            full |-> FALSE,
            empty |-> FALSE
        ]
    ];


define

AnyFull(self) == \E otherThread \in 2..NThreads:
        \/ (1 + (((threads[1].endr + 1) % sizeN) - 1)) = threads[otherThread].start

end define;           



    
fair process Thread \in 1..NThreads
\* This acts like a member variable and you can access it like one. But we're
\* actually creating an array with one element per process, and the "member
\* variable" we access is just the corresponding bucket in that array.

            
begin
WriterCheck:
    while TRUE do
        
        
        if threads[self].type = "writer" then
            threads[1].full := FALSE;
            if AnyFull(self) then
WriterFull:
                threads[1].full := TRUE
            end if;

WriterWrite:
        if threads[1].full = FALSE then
           sent[(1 + (((threads[1].endr + 1) % sizeN) - 1))] := [
                Reader |-> "not-read",
                Writer |-> "written"
            ];
            threads[1].endr := 1 + (((threads[1].endr + 1) % sizeN) - 1);
         
        end if;
    end if;
      
ReaderCheck:

    if threads[self].type = "reader" then
        threads[self].empty := FALSE;  
        if threads[self].start = threads[1].endr then
ReaderEmpty:
            threads[self].empty := TRUE;
        end if;
ReaderChecked:
        if threads[self].empty = FALSE then
ReaderNotEmpty:
            sent[threads[self].start].Reader := "read";
            threads[self].start := 1 + (((threads[self].start + 1) % sizeN) - 1);
           
            
            
        end if;
    end if;

    end while;
    
end process;
        
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "32eb6a15" /\ chksum(tla) = "193b16e0")
VARIABLES sent, types, threads, pc

(* define statement *)
AnyFull(self) == \E otherThread \in 2..NThreads:
        \/ (1 + (((threads[1].endr + 1) % sizeN) - 1)) = threads[otherThread].start


vars == << sent, types, threads, pc >>

ProcSet == (1..NThreads)

Init == (* Global variables *)
        /\ sent =      [thread \in 1..size |-> [
                           Writer |-> "not-written",
                           Reader |-> "not-read"
                    ]
                  ]
        /\ types = {"reader", "writer"}
        /\ threads =           [
                         thread \in 1..NThreads |-> [
                     
                             type |-> assigned[thread],
                             start |-> 1,
                             endr |-> 1,
                             full |-> FALSE,
                             empty |-> FALSE
                         ]
                     ]
        /\ pc = [self \in ProcSet |-> "WriterCheck"]

WriterCheck(self) == /\ pc[self] = "WriterCheck"
                     /\ IF threads[self].type = "writer"
                           THEN /\ threads' = [threads EXCEPT ![1].full = FALSE]
                                /\ IF AnyFull(self)
                                      THEN /\ pc' = [pc EXCEPT ![self] = "WriterFull"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "WriterWrite"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "ReaderCheck"]
                                /\ UNCHANGED threads
                     /\ UNCHANGED << sent, types >>

ReaderCheck(self) == /\ pc[self] = "ReaderCheck"
                     /\ IF threads[self].type = "reader"
                           THEN /\ threads' = [threads EXCEPT ![self].empty = FALSE]
                                /\ IF threads'[self].start = threads'[1].endr
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ReaderEmpty"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ReaderChecked"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "WriterCheck"]
                                /\ UNCHANGED threads
                     /\ UNCHANGED << sent, types >>

ReaderChecked(self) == /\ pc[self] = "ReaderChecked"
                       /\ IF threads[self].empty = FALSE
                             THEN /\ pc' = [pc EXCEPT ![self] = "ReaderNotEmpty"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "WriterCheck"]
                       /\ UNCHANGED << sent, types, threads >>

ReaderNotEmpty(self) == /\ pc[self] = "ReaderNotEmpty"
                        /\ sent' = [sent EXCEPT ![threads[self].start].Reader = "read"]
                        /\ threads' = [threads EXCEPT ![self].start = 1 + (((threads[self].start + 1) % sizeN) - 1)]
                        /\ pc' = [pc EXCEPT ![self] = "WriterCheck"]
                        /\ types' = types

ReaderEmpty(self) == /\ pc[self] = "ReaderEmpty"
                     /\ threads' = [threads EXCEPT ![self].empty = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "ReaderChecked"]
                     /\ UNCHANGED << sent, types >>

WriterWrite(self) == /\ pc[self] = "WriterWrite"
                     /\ IF threads[1].full = FALSE
                           THEN /\ sent' = [sent EXCEPT ![(1 + (((threads[1].endr + 1) % sizeN) - 1))] =                                                     [
                                                                                                             Reader |-> "not-read",
                                                                                                             Writer |-> "written"
                                                                                                         ]]
                                /\ threads' = [threads EXCEPT ![1].endr = 1 + (((threads[1].endr + 1) % sizeN) - 1)]
                           ELSE /\ TRUE
                                /\ UNCHANGED << sent, threads >>
                     /\ pc' = [pc EXCEPT ![self] = "ReaderCheck"]
                     /\ types' = types

WriterFull(self) == /\ pc[self] = "WriterFull"
                    /\ threads' = [threads EXCEPT ![1].full = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "WriterWrite"]
                    /\ UNCHANGED << sent, types >>

Thread(self) == WriterCheck(self) \/ ReaderCheck(self)
                   \/ ReaderChecked(self) \/ ReaderNotEmpty(self)
                   \/ ReaderEmpty(self) \/ WriterWrite(self)
                   \/ WriterFull(self)

Next == (\E self \in 1..NThreads: Thread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NThreads : WF_vars(Thread(self))

\* END TRANSLATION 

\*
\*
\*ProcSet == (1..NThreads)
\*
\*
\*
\*
\*
\*               
\*    
\*Init == (* Global variables *)
\*    /\ counter = "init"
\*    /\ step = 0
\*    /\ sent = [
\*        thread \in 1..size |-> [
\*               Writer |-> "not-written",
\*               Reader |-> "not-read"
\*        ]
\*      ]
\*    /\ threads = [
\*        thread \in 1..NThreads |-> [
\*    \* We create a thread proportion according to the assigned list
\*            type |-> assigned[thread],
\*            start |-> 1,
\*            endr |-> 1
\*        ]
\*      ]
\*   /\ pc = [self \in ProcSet |-> IF assigned[self] = "writer" THEN "WriterCheck" ELSE "ReaderCheck"]
\*
\*
\*\*Loop(self) == /\ pc[self] = "Loop"
\*\*              /\ IF /\ forks[LeftFork(self)].holder = self
\*\*                    /\ ~forks[LeftFork(self)].clean
\*\*                    THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] =                          [
\*\*                                                                           holder |-> LeftPhilosopher(self),
\*\*                                                                           clean |-> TRUE
\*\*                                                                       ]]
\*\*                    ELSE /\ IF /\ forks[RightFork(self)].holder = self
\*\*                               /\ ~forks[RightFork(self)].clean
\*\*                               THEN /\ forks' = [forks EXCEPT ![RightFork(self)] =                           [
\*\*                                                                                       holder |-> RightPhilosopher(self),
\*\*                                                                                       clean |-> TRUE
\*\*                                                                                   ]]
\*\*                               ELSE /\ TRUE
\*\*                                    /\ forks' = forks
\*\*              /\ IF hungry[self]
\*\*                    THEN /\ IF CanEat(self)
\*\*                               THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
\*\*                               ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
\*\*                    ELSE /\ pc' = [pc EXCEPT ![self] = "Think"]
\*\*              /\ UNCHANGED hungry
\*
\*
\*
\*Full(self) == \A thread \in 2..NThreads:
\*                    \/ threads[thread].start = (1 + ((threads[1].endr + 1) % size))
\*
\*Empty(self) == threads[self].start = threads[1].endr
\*
\*\*/\ IF ~(Len(sent) = size) THEN
\*\*                    /\ threads' = threads
\*\*                    /\ sent' = sent
\*\*                    /\ pc' = pc
\*\*                    /\ counter' = "finished"
\*\*                    /\ step' = step
\*\*                 ELSE 
\*
\*ThreadWorker(self) == 
\*                    /\ IF ~Empty(self)
\*                       THEN
\*                            /\ threads' = [threads EXCEPT ![self] = [
\*                                start |-> 1 + ((threads[self].start + 1) % size),
\*                                type |-> (threads[self].type),
\*                                endr |-> (threads[self].endr) 
\*                               ]]
\*                            /\ sent' = [sent EXCEPT ![threads[self].start].Reader = "read"]
\*                            /\ pc' = pc
\*                            /\ step' = step
\*                            /\ counter = "read"
\*                        ELSE (* Do nothing *)
\*                            /\ threads' = threads
\*                            /\ sent' = sent
\*                            /\ pc' = pc
\*                            /\ counter' = "empty-cannot-read"
\*                            /\ step' = step
\*                    \/ IF ~Full(self)
\*                       THEN 
\*                           (* [s EXCEPT ![1] = FALSE] *)
\*                            /\ threads' = [threads EXCEPT ![1] = [
\*                                endr |-> 1 + ((threads[1].endr + 1) % size),
\*                                type |-> (threads[1].type),
\*                                start |-> (threads[1].start)
\*                               ]]
\*                            /\ sent' = [sent EXCEPT ![threads[1].endr] = [
\*                                Writer |-> "written",
\*                                Reader |-> "not-read"
\*                               ]]
\*                            /\ pc' = pc
\*                            /\ counter' = "written-step"
\*                            /\ step' = step
\*                       ELSE (* Do nothing *)
\*                        /\ threads' = threads
\*                        /\ sent' = sent
\*                        /\ pc' = pc
\*                        /\ counter' = "full-cannot-write"
\*                        /\ step' = step
\*                        
\*                    
\*           
\*
\*                 
\*                      
\*Next == (\E self \in 1..NThreads: ThreadWorker(self))
\*----
\*
\*
\*Spec == /\ Init
\*        /\ [][Next]_vars
\*        /\ \E self \in 1..NThreads : WF_vars(ThreadWorker(self))
\*        
\*EndAboveStart == \A thread \in 1..NThreads:
\*                       /\ threads[1].endr >= threads[thread].start
\*AllRead ==
\*   \E item \in sent:
\*        /\ item.Reader = "read"         
\*
====
