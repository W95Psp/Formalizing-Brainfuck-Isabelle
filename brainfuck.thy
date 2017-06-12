theory brainfuck
imports Main "~~/src/HOL/Word/Word" "~~/src/HOL/IMP/Star"
begin
    (* In this file, I formalize basic construction of brainfuck and an implementation of fibonnaci (modulo 256!) *)
    (* Output is treated as integers, no ASCII support *)
    (* We consider here an infinite tape (but still, in my implementation, there is a way to handle finite looping tapes) *)
  
    (* We define brainfuck instructions *)
    (* To simplify proofs, I add a (Loop "Instr list"): the parser just need to deal with that *)
    (* Still, it is exaclty brainfuck (nothing more nothing less): the Loop construct is direct *)
    datatype Instr = MoveLeft | MoveRight | Loop "Instr list" | Incr | Decr | Print | Input
    fun split :: "string ⇒ string ⇒ nat ⇒ string × string" where
        "split bef [] _ = (bef, [])" |
        "split bef (c # tail) 0 = 
        (if (c = CHR ''['') then split (bef @ [c]) tail 1 else
         if (c = CHR '']'') then (bef, tail) else split (bef @ [c]) tail 0)" |
        "split bef (c # tail) n = split (bef @ [c]) tail 
        (if (c = CHR ''['') then n+1 else
         if (c = CHR '']'') then n-1 else n)"

    function parse :: "string ⇒ Instr list" where
    "parse '''' = []" |
    "parse (c # tail) = (let l = parse tail in
        (if (c = CHR ''<'') then (MoveLeft # l) else
        if (c = CHR ''>'') then (MoveRight # l) else
        if (c = CHR ''['') then 
            (let (a,b) = split [] tail 0 in (Loop (parse a)) # parse b)
        else
        if (c = CHR ''+'') then (Incr # l) else
        if (c = CHR ''-'') then (Decr # l) else
        if (c = CHR ''.'') then (Print # l) else
        if (c = CHR '','') then (Input # l) else l))"
    by pat_completeness auto
    termination sorry (* We really don't care about proving the parser correct *)
    value "parse '''++]++''"
      
    (* Now, we define a byte, a memory, and a state *)
    type_synonym byte = "8 word" (* so values are positive integer less than 255 *)
    lemma "(256 :: byte) = 0" by simp
    (* A memory is like that LEFT CURRENT RIGHT, with LEFT and RIGHT some lists of bytes *)
    (* If we want to make a finite list, then we would need to set RIGHT = rev LEFT for instance, but I did not tried that *)
    datatype mem = Mem "byte list" byte "byte list" 
    (* The state has some given input, some output, and a memory *)
    datatype State = State "byte list" "byte list" mem

    (* We define by induction a small step relation *)
    (* There are two cases for right and left, in order to handle cases where there is nothing on the left or on the right (nothing means 0 0 0 0 etc.) *)
    inductive
        smallStep :: "Instr list * State ⇒ Instr list * State ⇒ bool"  (infix "→" 55) 
    where
        LeftNone:  "([MoveLeft], State inps outs (Mem [] c r)) → ([], State inps outs (Mem [] 0 (c#r)))" |
        LeftSmth:  "([MoveLeft], State inps outs (Mem (v#l) c r)) → ([], State inps outs (Mem l v (c#r)))"  |
        RightNone: "([MoveRight], State inps outs (Mem l c [])) → ([], State inps outs (Mem (c#l) 0 []))" |
        RightSmth: "([MoveRight], State inps outs (Mem l c (v#r))) → ([], State inps outs (Mem (c#l) v r))" |
        Incr:      "([Incr], State inps outs (Mem l c r)) → ([], State inps outs (Mem l (c+1) r))" |
        Decr:      "([Decr], State inps outs (Mem l c r)) → ([], State inps outs (Mem l (c-1) r))" |
        Print:     "([Print], State inps outs (Mem l c r)) → ([], State inps (outs @ [c]) (Mem l c r))" |
        Input:     "([Input], State (v#inps) outs (Mem l c r)) → ([], State inps outs (Mem l v r))"  |
        Seq:      "(a, s) → (b, s') ⟹ (a@c, s) → (b@c, s')" |
        LoopT:		 "c ≠ 0 ⟹ ([Loop inside], State inps outs (Mem l c r)) → (inside @ [Loop inside], State inps outs (Mem l c r))" |
        LoopF:		 "c = 0 ⟹ ([Loop inside], State inps outs (Mem l c r)) → ([], State inps outs (Mem l c r))"
    
    (* Transitive closure *)
		abbreviation
			smallSteps :: "Instr list * State ⇒ Instr list * State ⇒ bool" (infix "→*" 55)
			where "x →* y == star smallStep x y"

(* Inversion rules *)
inductive_cases LeftNoneE[elim!]:	"([MoveLeft], State inps outs (Mem [] c r))		→ t" thm LeftNoneE
inductive_cases LeftSmthE[elim!]:	"([MoveLeft], State inps outs (Mem (v#l) c r))	→ t" thm LeftSmthE
inductive_cases RightNoneE[elim!]:	"([MoveRight], State inps outs (Mem l c []))	→ t" thm RightNoneE
inductive_cases RightSmthE[elim!]:	"([MoveRight], State inps outs (Mem l c (v#r)))	→ t" thm RightSmthE
inductive_cases IncrE[elim!]:		"([Incr], State inps outs (Mem l c r))			→ t" thm IncrE
inductive_cases DecrE[elim!]:		"([Decr], State inps outs (Mem l c r))			→ t" thm DecrE
inductive_cases PrintE[elim!]:		"([Print], State inps outs (Mem l c r))			→ t" thm PrintE
inductive_cases InputE[elim!]:		"([Input], State (v#inps) outs (Mem l c r))		→ t" thm InputE			
inductive_cases SeqE[elim]:			"(a@b, s) → t" thm SeqE
inductive_cases LoopE[elim]:		"([Loop inside], State inps outs (Mem l c r)) → t" thm LoopE

(* when you have a →* b, you can add instructions at the end of a and b *)
lemma star_seq: "(c1,s) →* (c1',s') ⟹ (c1@x,s) →* (c1'@x,s')"
	apply(induction rule: star_induct)
	 apply(simp)
	apply(rename_tac i1 s1 i2 s2 iN sN)
		apply(metis Seq star.step)
	done

lemma "⟦(list1, s0) →* ([], s1) ; (list2, s1) →* ([], s2)⟧ ⟹ (list1 @ list2, s0) →* ([], s2)"
	by (metis append_Nil star_seq star_trans)

(* different lemma to replace easily in star_seq/Seq like situation *)
lemma link_two_smallsteps: "⟦a → b ; b → c⟧ ⟹ a →* c"
	by (meson star.simps)
lemma link_smallstep_star: "⟦a → b ; b →* z⟧ ⟹ a →* z"
	by (meson star.simps)
lemma link_star_star: "⟦a →* b ; b →* z⟧ ⟹ a →* z"
	by (meson star_trans)
lemma link_star_smallstep: "⟦a →* b ; b → z⟧ ⟹ a →* z"
	by (meson star_trans star.simps)
	  
(* Some unfolding rules: apply the behaviour of some operators *)
lemma UnfoldDecr:"(Decr#li, (State inps outs (Mem l c r))) → (li, (State inps outs (Mem l (c-1) r)))"
	by (metis Decr Seq append_Cons append_Nil)
lemma UnfoldRightSmth: "(MoveRight#li, State inps outs (Mem l c (n#r)))
  → (li, State inps outs (Mem (c#l) n r))"
  by (metis RightSmth Seq append_Cons append_Nil)
lemma UnfoldRightNone: "(MoveRight#li, State inps outs (Mem l c []))
  → (li, State inps outs (Mem (c#l) 0 []))"
  by (metis (full_types) RightNone Seq append_Cons append_Nil)
lemma UnfoldIncr: "(Incr#li, State inps outs (Mem l c r))
  → (li, State inps outs (Mem l (c+1) r))"
  by (metis (full_types) Incr Seq append_Cons append_Nil)
lemma UnfoldLeftSmth: "(MoveLeft#li, State inps outs (Mem (n#l) c r))
  → (li, State inps outs (Mem l n (c#r)))"
  by (metis LeftSmth Seq append_Cons append_Nil)
lemma UnfoldLeftNone: "(MoveLeft#li, State inps outs (Mem [] c r))
  → (li, State inps outs (Mem [] 0 (c#r)))"
  by (metis (full_types) LeftNone Seq append_Cons append_Nil)

(* Some useful pieces of code to reuse in bigger things *)
definition CodeResetCurrent :: "Instr list" where "CodeResetCurrent = [Loop [Decr]]"
definition CodeOneCopyOnRight :: "Instr list" where "CodeOneCopyOnRight = [Loop [Decr, MoveRight, Incr, MoveLeft]]"
definition CodeTwoCopiesOnRight :: "Instr list" where "CodeTwoCopiesOnRight = [Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]]"
definition CodeMoveTwoLeft :: "Instr list" where "CodeMoveTwoLeft = [Loop [Decr, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight]]"
definition CodeDuplicateRight :: "Instr list" where "CodeDuplicateRight = CodeTwoCopiesOnRight@[MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft]"

(* Make smallStep executable *)
(* This is not working, I have no clue why (value "a → b" is jut returning some type signature, as soon as I add some loop logic in my small step inductive definition) *)
code_pred smallStep .
abbreviation emptyState :: "State" where "emptyState == State [] [] (Mem [] 0 [])"
value "(parse ''+'', emptyState) → ([], State [] [] (Mem [] 1 []))"
  
(* Function to work with memory easier*)
(* nMem represent a memory a flat and "tape-like" way *)
(* Usage: "nMem l r [1,2,3,4,5] 3" will represent the tape [...l, 1, 2, 3, 4, 5, r...] with the cursor on 4 (3 means 3 position on given array) *)
  fun nMem :: "byte list ⇒ byte list ⇒ byte list ⇒ nat ⇒ mem" where
    "nMem l r middle pos = (Mem ((rev (take pos middle)) @ l) (nth middle pos) (drop (pos + 1) middle @ r))"
  (*Example:*) value "nMem l r [a,0,b,0] 2"
	
(* Proof of CodeResetCurrent *)
  lemma resetCurrentCell_sub:"1 + c ≠ 0 ⟹ 
  ([Loop [Decr]], State inps outs (Mem l c r)) →* ([], State inps outs (Mem l 0 r))
   ⟹ ([Loop [Decr]], State inps outs (Mem l (1 + c) r)) →* ([], State inps outs (Mem l 0 r))"
    apply(drule LoopT[where inside="[Decr]" and inps=inps and outs=outs and l=l and r=r])
    apply(insert UnfoldDecr[where li="[Loop [Decr]]" and inps=inps and outs=outs and l=l and r=r and c="c+1"])
    apply(auto)
    apply(metis (no_types, hide_lams) add.commute star_trans link_two_smallsteps)
  done
  lemma resetCurrentCellSimple:"([Loop [Decr]], (State inps outs (Mem l c r))) →* ([], State inps outs (Mem l 0 r))"
    by (induction c,simp add:LoopF,simp add:resetCurrentCell_sub)
  lemma resetCurrentCell:"(Loop [Decr]#li, (State inps outs (Mem l c r))) →* (li, State inps outs (Mem l 0 r))"
    by (metis append_Cons append_Nil resetCurrentCellSimple star_seq)
  
	
	
value "parse ''+>>+<<<<++++++[->>[<+>>+<-]<[->+<]>>>[->+<]>[-<<<+>>>]<<[->+<]<.<<]''"
		
(* Proof of CodeOneCopyOnRight *)
  lemma oneCopyOnRight_sub_sub: "1 + c ≠ 0 ⟹ ([Loop [Decr, MoveRight, Incr, MoveLeft]], State inps outs (Mem l (1 + c) (n # r))) →*
                  ([Loop [Decr, MoveRight, Incr, MoveLeft]], State inps outs (Mem l c ((n+1) # r)))"
    apply(drule LoopT[where inside="[Decr, MoveRight, Incr, MoveLeft]" and inps=inps and outs=outs and l=l and r="n#r"], auto)
    apply(insert UnfoldDecr[where li="[MoveRight, Incr, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft]]" and l=l and c="c+1" and r="n#r" and inps=inps and outs=outs])
      apply(insert UnfoldRightSmth[where li="[Incr, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft]]" and l=l and c="c" and r="r" and n=n and inps=inps and outs=outs])
      apply(insert UnfoldIncr[where li="[MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft]]" and l="(c)#l" and c=n and r=r and inps=inps and outs=outs])
    apply(insert UnfoldLeftSmth[where li="[Loop [Decr, MoveRight, Incr, MoveLeft]]" and l="l" and c=n and n=c and r=r and inps=inps and outs=outs],auto)
    apply (simp add: UnfoldLeftSmth add.commute star.step)
    done
  lemma oneCopyOnRight_sub:"1 + c ≠ 0 ⟹
            (∀n. ([Loop [Decr, MoveRight, Incr, MoveLeft]], State inps outs (Mem l c (n # r))) →* ([], State inps outs (Mem l 0 ((n + c) # r)))) ⟹
           ([Loop [Decr, MoveRight, Incr, MoveLeft]], State inps outs (Mem l (1 + c) (n # r))) →* ([], State inps outs (Mem l 0 ((n + (1 + c)) # r)))"
    apply(drule oneCopyOnRight_sub_sub[where inps=inps and l=l and r=r and n=n and outs=outs])
    apply(drule spec[where x="n+1"])
    apply (simp only:add.commute add.left_commute)
      apply(drule link_star_star, auto)
    done
  lemma oneCopyOnRight: "([Loop [Decr, MoveRight, Incr, MoveLeft]], State inps outs (Mem l c (n # r))) →* ([], State inps outs (Mem l 0 ((n+c)#r)))"
    by(induction c arbitrary: n, simp add:LoopF, simp add:oneCopyOnRight_sub)
  lemma twoCopiesOnRight_inside:"([Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem l (c+1) (a # b # r))) →* 
                ([], State inps outs (Mem l c ((1+a) # (1+b) # r)))"
  proof -
    have "([MoveLeft, MoveLeft], State inps outs (Mem ((1 + a) # c # l) (b + 1) r)) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (metis UnfoldLeftSmth add.commute link_two_smallsteps)
    then have "([MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem (c # l) (1 + a) (b # r))) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (meson UnfoldIncr UnfoldRightSmth link_smallstep_star)
    then have "([MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem (c # l) (a + 1) (b # r))) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (simp add: add.commute)
    then have "([MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem l c (a # b # r))) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (meson UnfoldIncr UnfoldRightSmth link_smallstep_star)
    then have "([MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem l (1 + c - 1) (a # b # r))) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (simp)
    then have "([Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem l (1 + c) (a # b # r))) →* ([], State inps outs (Mem l c ((1 + a) # (1 + b) # r)))"
      by (meson UnfoldDecr link_smallstep_star)
    then show ?thesis
      by (simp add: add.commute)
  qed

(* Proof of CodeTwoCopiesOnRight *)
  lemma twoCopiesOnRight_sub_sub: "1 + c ≠ 0 ⟹
        ([Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]], State inps outs (Mem l (c+1) (a # b # r)))
    →* ([Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]], State inps outs (Mem l c ((a+1) # (b+1) # r)))
      "
    apply(drule LoopT[where inside="[Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]" and inps=inps and outs=outs and l=l and r="a#b#r"], auto)
    apply(insert twoCopiesOnRight_inside[where outs=outs and inps=inps and l=l and r=r and c=c and a=a and b=b])
    apply(drule star_seq[where x="[Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]]"], auto)
    apply (simp only:add.commute add.left_commute)
      apply(drule link_smallstep_star, auto)
  done
  lemma twoCopiesOnRight_sub: " 1 + c ≠ 0 ⟹
                 (∀v1 v2. ([Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]], State inps outs (Mem l c (v1 # v2 # r))) →*
                           ([], State inps outs (Mem l 0 ((v1 + c) # (v2 + c) # r)))) ⟹
                 ([Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]], State inps outs (Mem l (1 + c) (v1 # v2 # r))) →*
                 ([], State inps outs (Mem l 0 ((v1 + (1 + c)) # (v2 + (1 + c)) # r)))"
    apply(drule twoCopiesOnRight_sub_sub[where a=v1 and b=v2 and inps=inps and outs=outs and l=l and r=r])
      apply(drule spec[where x="v1+1"], drule spec[where x="v2+1"])
    apply (simp only:add.commute add.left_commute)
      apply(drule link_star_star, auto)
    done
  lemma twoCopiesOnRight: "([Loop [Decr, MoveRight, Incr, MoveRight, Incr, MoveLeft, MoveLeft]], State inps outs (Mem l c (a # b # r)))
              →* ([], State inps outs (Mem l 0 ((a+c)#(b+c)#r)))"
    apply(induction c arbitrary: a b, simp add:LoopF, simp add:twoCopiesOnRight_sub)
  done

(* Proof of CodeMoveTwoLeft *)
  lemma moveTwoLeft_inside:"([Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight], State inps outs (Mem (a # b # l) (c+1) r))
    →* ([], State inps outs (Mem (a # (b+1) # l) c r))"
    proof -
    have "([MoveRight, MoveRight], State inps outs (Mem l (b + 1) (a # c #r))) →* ([], State inps outs (Mem (a # (b+1) # l) c r))"
      by (metis UnfoldRightSmth link_two_smallsteps)
    then have "([MoveLeft, MoveLeft, Incr, MoveRight, MoveRight], State inps outs (Mem (a#b#l) c r)) →* ([], State inps outs (Mem (a # (b+1) # l) c r))"
      by (meson UnfoldIncr UnfoldLeftSmth link_smallstep_star)
    then have "([Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight], State inps outs (Mem (a#b#l) (c+1) r)) →*  ([], State inps outs (Mem (a # (b+1) # l) c r))"
      by (simp add:add.commute,metis (full_types) UnfoldDecr add_diff_cancel_left' link_smallstep_star)
    then show ?thesis
      by simp
  qed
  lemma moveTwoLeft_sub_sub: "1 + c ≠ 0 ⟹
        ([Loop [Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight]], State inps outs (Mem (a#b#l) (c+1) r))
    →* ([Loop [Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight]], State inps outs (Mem (a#(b+1)#l) c r))
      "
    apply(drule LoopT[where inside="[Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight]" and inps=inps and outs=outs and l="a#b#l" and r=r], auto)
    apply(insert moveTwoLeft_inside[where outs=outs and inps=inps and l=l and r=r and c=c and a=a and b=b])
    apply(drule star_seq[where x="[Loop [Decr, MoveLeft,  MoveLeft, Incr, MoveRight, MoveRight]]"], auto)
    apply (simp only:add.commute add.left_commute)
      apply(drule link_smallstep_star, auto)
  done
  lemma moveTwoLeft_sub: "1 + c ≠ 0 ⟹
               (∀ a b. ([Loop [Decr, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight]], State inps outs (Mem (a # b # l) c r)) →*
                       ([], State inps outs (Mem (a # (b+c) # l) 0 r))) ⟹
               ([Loop [Decr, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight]], State inps outs (Mem (a # b # l) (1 + c) r)) →*
               ([], State inps outs (Mem (a # (b + (1 + c)) # l) 0 r))"
    
    apply(drule moveTwoLeft_sub_sub[where a=a and b=b and inps=inps and outs=outs and l=l and r=r])
      apply(drule spec[where x=a], drule spec[where x="b+1"])
    apply (simp only:add.commute add.left_commute)
      apply(frule link_star_star, auto)
    done
  lemma moveTwoLeft: "([Loop [Decr, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight]], State inps outs (Mem (a # b # l) c r))
              →* ([], State inps outs (Mem (a#(b+c)#l) 0 r))"
    apply(induction c arbitrary: a b, simp add:LoopF, simp add:moveTwoLeft_sub)
    done
  

(* We will get a=a+c and b=b+c at some point, then we move b+c to c *)
(*CodeTwoCopiesOnRight@[MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft] *)
lemma DuplicateRight: "
  (CodeTwoCopiesOnRight@[MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (nMem l r [c,a,b] 0))→*
  ([], State inps outs (nMem l r [b+c, a+c, 0] 0))
"
 apply(insert twoCopiesOnRight[where inps=inps and outs=outs and a=a and b=b and c=c and l=l and r=r])
  apply(drule star_seq[where x="[MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft]"])
    apply(insert UnfoldRightSmth[where inps=inps and li="MoveRight#CodeMoveTwoLeft@[MoveLeft, MoveLeft]" and n="a+c" and outs=outs and c=0 and l=l and r="(b+c)#r"])
  apply(auto)
  apply(drule link_star_smallstep, auto)
    apply(thin_tac "(MoveRight # MoveRight # CodeMoveTwoLeft @ [MoveLeft, MoveLeft], State inps outs (Mem l 0 ((a + c) # (b + c) # r))) →
    (MoveRight # CodeMoveTwoLeft @ [MoveLeft, MoveLeft], State inps outs (Mem (0 # l) (a + c) ((b + c) # r)))")
  apply(insert UnfoldRightSmth[where inps=inps and li="CodeMoveTwoLeft@[MoveLeft, MoveLeft]" and n="b+c" and outs=outs and c="a+c" and l="0#l" and r="r"])
  apply(drule link_star_smallstep, auto)
    apply(thin_tac "(MoveRight # CodeMoveTwoLeft @ [MoveLeft, MoveLeft], State inps outs (Mem (0 # l) (a + c) ((b + c) # r))) →
    (CodeMoveTwoLeft @ [MoveLeft, MoveLeft], State inps outs (Mem ((a + c) # 0 # l) (b + c) r))")
  apply(insert moveTwoLeft[where inps=inps and outs=outs and l=l and r=r and a="a+c" and b=0 and c="b+c"])
  apply(drule star_seq[where x="[MoveLeft, MoveLeft]"]) back
  apply(auto)
    apply(simp add:CodeMoveTwoLeft_def)
  apply(drule link_star_star, auto)
    apply(thin_tac "([Loop [Decr, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight], MoveLeft, MoveLeft], State inps outs (Mem ((a + c) # 0 # l) (b + c) r)) →*
    ([MoveLeft, MoveLeft], State inps outs (Mem ((a + c) # (b + c) # l) 0 r))")
  apply(insert UnfoldLeftSmth[where inps=inps and li="[MoveLeft]" and outs=outs and n="a+c" and l="(b+c)#l" and c=0 and r=r])
  apply(drule link_star_smallstep, auto)
    apply(thin_tac "([MoveLeft, MoveLeft], State inps outs (Mem ((a + c) # (b + c) # l) 0 r)) → ([MoveLeft], State inps outs (Mem ((b + c) # l) (a + c) (0 # r)))")
  apply(insert UnfoldLeftSmth[where inps=inps and li="[]" and outs=outs and n="b+c" and l="l" and c="a+c" and r="0#r"])
  apply(drule link_star_smallstep, simp)
  apply(thin_tac " ([MoveLeft], State inps outs (Mem ((b + c) # l) (a + c) (0 # r))) → ([], State inps outs (Mem l (b + c) ((a + c) # 0 # r))) ")
    by(simp add:CodeTwoCopiesOnRight_def)

lemma DuplicateRight0 : "(CodeDuplicateRight, State inps outs (nMem l r [c,0,0] 0)) →* ([], State inps outs (nMem l r [c,c,0] 0))"
  apply(insert DuplicateRight[where inps=inps and outs=outs and c=c and a=0 and b=0 and l=l and r=r])
    by(simp add: CodeDuplicateRight_def)

lemma conditionalF_sub: "([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r))) →
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) ⟹
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) →
    ([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r))
⟹
    ([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r))) →*
    ([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r))"
  by(drule link_two_smallsteps, auto)
lemma conditionalF_sub2: "
 ([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r))) →*
    ([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) ⟹
    ([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) → ([Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r)))
⟹
  ([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r))) →*
([Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r)))
    "
  by(drule link_star_smallstep, auto)
lemma conditionalT_sub:" ([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (n # r))) →
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) ⟹
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →
    (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r))
⟹
  ([MoveRight, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (n # r))) →*
  (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r))"
  by(drule link_two_smallsteps, auto)

lemma conditionalT_sub2 : "
  (cond, State inps outs (Mem (0 # 1 # l) n r)) →* ([], State inps' outs' (Mem (0 # 1 # l') n r')) ⟹
  (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
  ([MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (0 # 1 # l') n r'))
"
  using star_seq by fastforce
lemma conditionalT_sub3: "
  (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (0 # 1 # l') n r')) ⟹
    ([MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (0 # 1 # l') n r')) →
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))
⟹
  (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))
"
  using link_star_smallstep by blast
lemma conditionalT_sub4: "
    (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) ⟹
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) →
    ([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))
⟹
     (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r))→*
([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))
"
  using link_star_smallstep by blast
lemma conditionalT_sub5: "(cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) ⟹
    ([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) →
    ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r')))
⟹
    (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r')))
"
  using link_star_smallstep by blast
lemma conditionalT_sub6: "(cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) ⟹
    ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) →
    ([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) 
⟹(cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
   ([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) 
    "
  using link_star_smallstep by blast
lemma conditionalT_sub7: "(cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) ⟹
    ([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) →
    ([Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))
⟹ (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →*
    ([Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))"
  using link_star_smallstep by blast
lemma conditionalT: "
      n≠0 ⟹ (cond, State inps outs (nMem l r [1,0,n] 2)) →* ([], State inps' outs' (nMem l' r' [1,0,n] 2)) ⟹
      ([MoveRight, Loop (cond@[MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (nMem l r [1,0,n] 1))
      →* ([], State inps' outs' (nMem l' r' [1,0,n] 1))"
  apply(auto)
  apply(insert UnfoldRightSmth[where inps=inps and outs=outs
          and n=n and l="1#l" and r=r and c=0 and li="[Loop (cond@[MoveLeft]), MoveLeft, Loop [MoveRight]]"])
  apply(drule LoopT[where inps=inps and outs=outs and inside="cond @ [MoveLeft]" and l="(0 # 1 # l)" and r=r])
  apply(auto)
  apply(drule Seq[where c="[MoveLeft, Loop [MoveRight]]"],auto) back
  apply(drule conditionalT_sub, auto)
    apply(thin_tac " ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r)) →
    (cond @ [MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) n r))")
  apply(drule conditionalT_sub2)
  apply(erule link_star_star)
  apply(insert UnfoldLeftSmth[where inps=inps' and outs=outs' and c=n and l="1#l'" and r=r' and n=0 and li="[Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]]"])
  apply(drule conditionalT_sub3, auto)
    apply(thin_tac "([MoveLeft, Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (0 # 1 # l') n r')) →
    ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))")
      apply(insert LoopF[where inside="cond @ [MoveLeft]" and inps=inps' and outs=outs' and l="1#l'" and r="n#r'" and c=0], auto)
  apply(drule Seq[where c="[MoveLeft, Loop [MoveRight]]"],auto)
  apply(drule conditionalT_sub4, auto)
    apply(thin_tac "([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) →
    ([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))")
  apply(insert UnfoldLeftSmth[where inps=inps' and outs=outs' and c=0 and r="n#r'" and l="l'" and n=1 and li="[Loop [MoveRight]]"])
      apply(drule conditionalT_sub5, auto)
    apply(thin_tac " ([MoveLeft, Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r'))) →
    ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r')))")
  apply(insert LoopT[where inps=inps' and outs=outs' and inside="[MoveRight]" and l="l'" and c=1 and r="0#n#r'"], auto)
  apply(drule conditionalT_sub6, auto)
    apply(thin_tac " ([Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) →
    ([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r')))")
  apply(insert UnfoldRightSmth[where outs=outs' and inps=inps' and l=l' and c=1 and r="n#r'" and li="[Loop [MoveRight]]" and n=0])
  apply(drule conditionalT_sub7, auto)
    apply(thin_tac "([MoveRight, Loop [MoveRight]], State inps' outs' (Mem l' 1 (0 # n # r'))) →
    ([Loop [MoveRight]], State inps' outs' (Mem (1 # l') 0 (n # r')))")
  apply(insert LoopF[where inps=inps' and outs=outs' and inside="[MoveRight]" and c=0 and l="(1 # l')" and r="n#r'"], simp)
  using link_star_smallstep by blast
    
  
lemma conditionalF: "
      n=0 ⟹
      ([MoveRight, Loop (cond@[MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (nMem l r [1,0,n] 1))
      →* ([], State inps outs (nMem l r [1,0,n] 1))"
  apply(auto)
  apply(insert UnfoldRightSmth[where inps=inps and outs=outs
          and n=n and l="1#l" and r=r and c=0 and li="[Loop (cond@[MoveLeft]), MoveLeft, Loop [MoveRight]]"])
  apply(simp)
  apply(frule LoopF[where inps=inps and outs=outs and inside="cond @ [MoveLeft]" and l="(0 # 1 # l)" and r=r])
  apply(auto)
  apply(drule Seq[where c="[MoveLeft, Loop [MoveRight]]"],auto) back
  apply(drule conditionalF_sub, auto)
    apply(thin_tac " ([Loop (cond @ [MoveLeft]), MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) →
    ([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r))")
  apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and c=0 and r=r and l="1#l" and n=0 and li="[Loop [MoveRight]]"])
    apply(drule conditionalF_sub2, auto)
  apply(thin_tac "([MoveLeft, Loop [MoveRight]], State inps outs (Mem (0 # 1 # l) 0 r)) → ([Loop [MoveRight]], State inps outs (Mem (1 # l) 0 (0 # r)))" )
  apply(frule LoopF[where inps=inps and outs=outs and inside="[MoveRight]" and l="(1 # l)" and r="0#r"], auto)
  by(drule link_star_smallstep,auto)

lemma LoadConstant_step : "(replicate n Incr, State inps outs (Mem l c r)) →* ([], State inps outs (Mem l (c + of_nat n) r)) ⟹
         (Incr # replicate n Incr, State inps outs (Mem l c r)) →* ([], State inps outs (Mem l (c + (1 + of_nat n)) r))"
proof -
  assume "(replicate n Incr, State inps outs (Mem l c r)) →* ([], State inps outs (Mem l (c + of_nat n) r))"
  then have "∀is. (replicate n Incr @ is, State inps outs (Mem l c r)) →* (is, State inps outs (Mem l (c + of_nat n) r))"
    by (metis (no_types) append_self_conv2 star_seq)
  then have "(replicate n Incr @ [Incr], State inps outs (Mem l c r)) →* ([], State inps outs (Mem l (c + of_nat n + 1) r))"
    by (meson Incr link_star_smallstep)
  then show ?thesis
    by (simp add: add.commute add.left_commute replicate_append_same)
qed
  
lemma LoadConstant : "(replicate n Incr, State inps outs (Mem l c r)) →* ([], State inps outs (Mem l (c + (of_nat n)) r))"
  by(induction n, auto, drule LoadConstant_step, auto)
    
lemma MoveNRight_sub : "∀ l . (replicate n MoveRight, State inps outs (Mem l 0 (replicate n 0 @ r))) →*
         ([], State inps outs (Mem (rev (take n (0 # replicate n 0)) @ l) ((0 # replicate n 0) ! n) r)) ⟹
         (MoveRight # replicate n MoveRight, State inps outs (Mem l 0 (0 # replicate n 0 @ r))) →*
         ([], State inps outs (Mem (rev (take n (0 # replicate n 0)) @ 0 # l) ((0 # replicate n 0) ! n) r))"
  apply(insert UnfoldRightSmth[where li="replicate n MoveRight" and inps=inps and outs=outs and l=l and r="replicate n 0 @ r" and n=0 and c=0])
  apply(drule spec[where x="0#l"])  
  by(drule link_smallstep_star, auto)
lemma MoveNRight : "(replicate n MoveRight, State inps outs (nMem l r (replicate (Suc n) 0) 0)) →* ([], State inps outs (nMem l r (replicate (Suc n) 0) n))"
  by(auto, induction n arbitrary:l, auto, simp add:MoveNRight_sub)

lemma revL: "0 # replicate n 0 = replicate n 0 @ [0]"
  by (simp add: replicate_append_same)
lemma revL2: "replicate n 0 @ 0 # l = 0 # replicate n 0 @ l"
  by (simp add: replicate_append_same)
lemma revL3: "(0 # replicate n 0) ! n = 0"
  by (metis less_Suc_eq nth_replicate replicate_Suc)
  
lemma MoveNLeft_sub : "(∀r. (replicate n MoveLeft, State inps outs (Mem (rev (take n (0 # replicate n 0)) @ l) ((0 # replicate n 0) ! n) r)) →*
                ([], State inps outs (Mem l 0 (replicate n 0 @ r)))) ⟹
           (MoveLeft # replicate n MoveLeft, State inps outs (Mem (rev (take n (0 # replicate n 0)) @ 0 # l) ((0 # replicate n 0) ! n) r)) →*
           ([], State inps outs (Mem l 0 (0 # replicate n 0 @ r)))"
  apply(simp add:revL)
  apply(simp add:revL2)
  apply(insert UnfoldLeftSmth[where li="replicate n MoveLeft" and inps=inps and outs=outs and l="(replicate n 0 @ l)" and r=r and n=0 and c=" ((0 # replicate n 0) ! n)"])
  apply(simp add:revL3)
  apply(drule spec[where x="0#r"])
  apply(simp add:revL2)
  by(drule link_smallstep_star, auto)
lemma MoveNLeft : "(replicate n MoveLeft, State inps outs (nMem l r (replicate (Suc n) 0) n)) →* ([], State inps outs (nMem l r (replicate (Suc n) 0) 0))"
  by(auto, induction n arbitrary:r, auto, simp add:MoveNLeft_sub)

    
value "parse ''[<+>>+<-]''"
lemma CopyRightAndLeft_body : "([MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr], State inps outs (Mem (a#l) c (b#r))) →*
          ([], State inps outs (Mem ((a+1)#l) (c-1) ((b+1)#r)))"
  apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and li="[Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]"
                          and n=a and l=l and r="b#r" and c=c])
  apply(insert UnfoldIncr[where inps=inps and outs=outs and li="[MoveRight, MoveRight, Incr, MoveLeft, Decr]"
                          and l=l and r="c#b#r" and c=a])
  apply(insert UnfoldRightSmth[where li="[MoveRight, Incr, MoveLeft, Decr]" and inps=inps and outs=outs and
                                r="b#r" and l=l and c="a+1" and n=c])
  apply(insert UnfoldRightSmth[where li="[Incr, MoveLeft, Decr]" and inps=inps and outs=outs and
                                r="r" and l="(a+1)#l" and c="c" and n=b])
  apply(insert UnfoldIncr[where inps=inps and outs=outs and li="[MoveRight, MoveRight, Incr, MoveLeft, Decr]"
                          and l=l and r="c#b#l" and c=a])
  apply(insert UnfoldIncr[where li="[MoveLeft, Decr]" and outs=outs and inps=inps and l="c#(a+1)#l" and r=r and c=b])
       apply(insert UnfoldLeftSmth[where li="[Decr]" and outs=outs and inps=inps and l="(a+1)#l" and n=c and r=r and c="b+1"])
  apply(insert UnfoldDecr[where li="[]" and outs=outs and inps=inps and l="(a + 1)#l" and r="(b+1)#r" and c="c"])
  by (meson UnfoldIncr UnfoldLeftSmth UnfoldRightSmth link_smallstep_star link_two_smallsteps)
    
lemma CopyRightAndLeft_sub: "1 + c ≠ 0 ⟹ ∀ a b .  ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) c (b # r))) →*
         ([], State inps outs (Mem ((a + c) # l) 0 ((b + c) # r))) ⟹
         ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r))) →*
         ([], State inps outs (Mem ((a + (1 + c)) # l) 0 ((b + (1 + c)) # r)))"
  apply(drule LoopT[where inside="[MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]" and
              inps=inps and outs=outs and l="a#l" and r="b#r" ])
  apply(simp)
  apply(insert CopyRightAndLeft_body[where inps=inps and outs=outs  and a=a and l=l and c="1+c"  and b=b and r=r], auto)
  apply(drule star_seq[where x="[Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]]"], auto)
  apply(drule spec[where x="a+1"], drule spec[where x="b+1"])
proof -
  assume a1: "([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r))) → ([MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr, Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r)))"
  assume a2: "([MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr, Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r))) →* ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem ((a + 1) # l) c ((b + 1) # r)))"
  assume "([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem ((a + 1) # l) c ((b + 1) # r))) →* ([], State inps outs (Mem ((a + 1 + c) # l) 0 ((b + 1 + c) # r)))"
  then have "([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem ((1 + a) # l) c ((1 + b) # r))) →* ([], State inps outs (Mem ((1 + (a + c)) # l) 0 ((1 + (b + c)) # r)))"
  by (simp add: add.commute add.left_commute)
  then have "∀p. ¬ p →* ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem ((1 + a) # l) c ((1 + b) # r))) ∨ p →* ([], State inps outs (Mem ((1 + (a + c)) # l) 0 ((1 + (b + c)) # r)))"
    by (meson link_star_star)
  then have "∃p. ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r))) → p ∧ p →* ([], State inps outs (Mem ((1 + (a + c)) # l) 0 ((1 + (b + c)) # r)))"
    using a2 a1 by (metis add.commute)
  then have "([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (Mem (a # l) (1 + c) (b # r))) →* ([], State inps outs (Mem ((1 + (a + c)) # l) 0 ((1 + (b + c)) # r)))"
    by (meson link_smallstep_star)
  then show ?thesis
    by (simp add: add.left_commute)
qed 
definition codeCopy3Left :: "Instr list" where
    "codeCopy3Left = [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]"
definition CopyRightAndLeft :: "Instr list" where
    "CopyRightAndLeft = [Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]]"
         
lemma CopyRightAndLeft : "([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr]], State inps outs (nMem l r [a, c, b] 1))
      →* ([], State inps outs (nMem l r [a+c, 0, b+c] 1))"
  by(induction c arbitrary: a b, auto simp add:LoopF, auto simp add:CopyRightAndLeft_sub)

lemma Copy3LeftInside:"([Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight], State inps outs (nMem l r [a,b,c,d] 3))
      →* ([], State inps outs (nMem l r [a+1,b,c,d-1] 3))"
  apply(auto)
  apply(insert UnfoldDecr[where inps=inps and outs=outs and li="[MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]"
		 and l="c # b # a # l" and r=r and c=d])
  apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and li="[MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]"
       and l="b # a # l" and r=r and c="d-1" and n=c])
  apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and li="[MoveLeft, Incr, MoveRight, MoveRight, MoveRight]"
       and l="(a # l)" and c=c and r="(d - 1)#r" and n=b])
  apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and li="[Incr, MoveRight, MoveRight, MoveRight]"
       and n=a and l=l and r="c#(d-1)#r" and c=b])
  apply(insert UnfoldIncr[where inps=inps and outs=outs and li="[MoveRight, MoveRight, MoveRight]"
       and l=l and r="b#c#(d-1)#r" and c=a])
  apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="[MoveRight, MoveRight]"
       and l="l" and n=b and r="c#(d-1)#r" and c="a+1"])
  apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="[MoveRight]"
       and l="(a+1)#l" and r="(d-1)#r" and c=b and n=c])
  apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="[]"
       and l="b#(a+1)#l" and r=r and c=c and n="d-1"])
  using link_smallstep_star link_two_smallsteps by presburger

lemma Copy3Left_sub: "1 + d ≠ 0 ⟹(∀a. ([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # a # l) d r)) →*
                 ([], State inps outs (Mem (c # b # (a + d) # l) 0 r))) ⟹
           ([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # a # l) (1 + d) r)) →*
           ([], State inps outs (Mem (c # b # (a + (1 + d)) # l) 0 r))
"
  apply(drule LoopT[where inside="[Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]"
                  and outs=outs and inps=inps and l="c#b#a#l" and r=r])
  apply(insert Copy3LeftInside[where inps=inps and outs=outs and l=l and r=r and c=c and a=a and b=b and d="1+d"], auto)
  apply(drule star_seq[where x="[Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]]"], auto)
  apply(drule spec[where x="a+1"])
proof -
  assume a1: "([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # (a + 1) # l) d r)) →* ([], State inps outs (Mem (c # b # (a + 1 + d) # l) 0 r))"
  assume a2: "([Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight, Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # a # l) (1 + d) r)) →* ([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # (a + 1) # l) d r))"
  assume a3: "([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # a # l) (1 + d) r)) → ([Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight, Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # a # l) (1 + d) r))"
  have "([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # (a + 1) # l) d r)) →* ([], State inps outs (Mem (c # b # (d + (a + 1)) # l) 0 r))"
    using a1 by (simp add: add.commute)
  then have "([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # (1 + a) # l) d r)) →* ([], State inps outs (Mem (c # b # (1 + (a + d)) # l) 0 r))"
    by (simp add: add.commute add.left_commute)
  then have "⋀p. ¬ p →* ([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (Mem (c # b # (1 + a) # l) d r)) ∨ p →* ([], State inps outs (Mem (c # b # (1 + (a + d)) # l) 0 r))"
    by (meson link_star_star)
  then show ?thesis
    using a3 a2 by (simp add: add.commute add.left_commute link_smallstep_star)
qed
    

    
    
    
lemma Copy3Left:"([Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight]], State inps outs (nMem l r [a,b,c,d] 3))
  →* ([], State inps outs (nMem l r [a+d,b,c,0] 3))"
  apply(induction d arbitrary:a, auto simp add:LoopF)
  by(simp add:Copy3Left_sub)
  
(* ######### Fibonnaci example ######### *)
    lemma FibPrepare: "(parse ''+>>+<<'', State inps outs (nMem l r [0,0,0,0,0] 1)) →*
        ([], State inps outs (nMem l r [0,1,0,1,0] 1))"
      apply(auto)
    proof -
      have "([MoveLeft, MoveLeft], State inps outs (Mem (0 # 1 # 0 # l) (0 + 1) (0 # r))) →* ([], State inps outs (Mem (0 # l) 1 (0 # 1 # 0 # r)))"
        by (metis UnfoldLeftSmth comm_monoid_add_class.add_0 link_two_smallsteps)
      then have "([MoveRight, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem (0 # l) 1 (0 # 0 # 0 # r))) →* ([], State inps outs (Mem (0 # l) 1 (0 # 1 # 0 # r)))"
        by (meson UnfoldIncr UnfoldRightSmth link_smallstep_star)
      then have "([MoveRight, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem (0 # l) (0 + 1) (0 # 0 # 0 # r))) →* ([], State inps outs (Mem (0 # l) 1 (0 # 1 # 0 # r)))"
        by simp
      then show "([Incr, MoveRight, MoveRight, Incr, MoveLeft, MoveLeft], State inps outs (Mem (0 # l) 0 (0 # 0 # 0 # r))) →* ([], State inps outs (Mem (0 # l) 1 (0 # 1 # 0 # r)))"
        by (meson UnfoldIncr link_smallstep_star)
    qed
    
    definition FibPart3::"Instr list " where
      "FibPart3 = [Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight],
      MoveLeft, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"
      
    definition FibPart2::"Instr list" where
      "FibPart2 = [MoveRight, MoveRight, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight]@FibPart3"
    lemma ToFibPart2:"[MoveRight, MoveRight, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight],
      MoveLeft, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft] = FibPart2"
      by (simp add: FibPart2_def FibPart3_def)
    
      
    value "parse ''[<+>>+<-] < [->+<] >       >> [->+<] > [-<<<+>>>] << [->+<] <''"
    value "parse ''   >> [->+<] > [-<<<+>>>] << [->+<] <''"
    lemma FibInsidePart1: "
    ([Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr], MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, MoveRight, MoveRight,
      Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight], MoveLeft, MoveLeft,
      Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft], State inps outs (nMem l r [0,a,0,b,0] 1))
      →*
      (FibPart2, State inps outs (Mem (0 # l) a (a # b # 0 # r)))"
      apply(simp)
      apply(insert CopyRightAndLeft[where inps=inps and outs=outs and l="l" and r="b#0#r" and a=0 and b=0 and c=a], auto)
      apply(drule star_seq[where x="[MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, MoveRight, MoveRight, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight,
      Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight], MoveLeft, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"])
      apply(auto)
      apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and l=l and r="a # b # 0 # r" and n=a and c=0
                and li="[Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, MoveRight, MoveRight, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight,
                Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight], MoveLeft, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"])
      apply(simp add:ToFibPart2)
        apply(insert oneCopyOnRight[where inps=inps and outs=outs and l=l and c=a and r="a#b#0#r" and n=0])
      apply(drule star_seq[where x="MoveRight # FibPart2"],auto) back
      apply(insert UnfoldRightSmth[where inps=inps and outs=outs and l=l and c=0 and r="a#b#0#r" and n=a
                and li="FibPart2"])
      using link_star_star by blast
    
    lemma FibInsidePart2: "(FibPart2, State inps outs (Mem (0 # l) a (a # b # 0 # r))) →* (FibPart3, State inps outs (Mem (0 # a # a # 0 # l) b r))"
      apply(auto simp add:FibPart2_def)
      apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="MoveRight # Loop [Decr, MoveRight, Incr, MoveLeft] # MoveRight # FibPart3"
              and l="0#l" and r="b#0#r" and c=a and n=a])
      apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="Loop [Decr, MoveRight, Incr, MoveLeft] # MoveRight # FibPart3"
              and l="a#0#l" and r="0#r" and c=a and n=b])
      apply(insert oneCopyOnRight[where inps=inps and outs=outs and l="a#a#0#l" and r=r and c=b and n=0])
      apply(drule star_seq[where x="MoveRight # FibPart3"], auto)
      apply(insert UnfoldRightSmth[where inps=inps and outs=outs and li="FibPart3"
              and l="a#a#0#l" and r="r" and c=0 and n=b])
      using link_smallstep_star link_star_smallstep by blast
    
    lemma FibInsidePart3 : "(FibPart3, State inps outs (Mem (0 # a # a # 0 # l) b r)) →*  ([], State inps outs (nMem l r [0,a+b,0,a,0] 1))"
      apply(auto simp add:FibPart3_def)
      apply(insert Copy3Left[where inps=inps and outs=outs and l="0#l" and c=0 and r=r and a="a" and b=a and d=b], auto)
        apply(drule star_seq[where x="[MoveLeft, MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft],MoveLeft]"], auto)
      apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and l="a#(a+b)#0#l" and r="r" and n=0 and c=0
                and li="[MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"])
      apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and l="(a+b)#0#l" and r="0#r" and n=a and c=0
                and li="[Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"])
      apply(insert oneCopyOnRight[where inps=inps and outs=outs and l="(a+b)#0#l" and r="0#r" and c=a and n=0])
            apply(drule star_seq[where x="[MoveLeft]"], auto) back
      apply(insert UnfoldLeftSmth[where inps=inps and outs=outs and l="0#l" and r="a#0#r" and n="a+b" and c=0
                and li="[]"])
      by (meson link_star_smallstep link_star_star)
    definition CodeFibInside :: "Instr list" where
      "CodeFibInside = [Loop [MoveLeft, Incr, MoveRight, MoveRight, Incr, MoveLeft, Decr], MoveLeft, Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, MoveRight, MoveRight,
      Loop [Decr, MoveRight, Incr, MoveLeft], MoveRight, Loop [Decr, MoveLeft, MoveLeft, MoveLeft, Incr, MoveRight, MoveRight, MoveRight], MoveLeft, MoveLeft,
      Loop [Decr, MoveRight, Incr, MoveLeft], MoveLeft]"
      
    lemma FibInside: "(CodeFibInside, State inps outs (nMem l r [0,a,0,b,0] 1)) →* ([], State inps outs (nMem l r [0,a+b,0,a,0] 1))"
      apply(simp add:CodeFibInside_def)
      apply(insert FibInsidePart1[where l=l and r=r and inps=inps and outs=outs and a=a and b=b])
      apply(insert FibInsidePart2[where l=l and r=r and inps=inps and outs=outs and a=a and b=b])
      apply(insert FibInsidePart3[where l=l and r=r and inps=inps and outs=outs and a=a and b=b])
        apply(simp add:FibPart2_def)
      apply(simp add:FibPart3_def)
      using link_star_star by blast
    
    (* Now, we implement a fib funtion in Isabelle *)
    fun fib :: "nat ⇒ nat" where
      "fib 0 = 2" |
      "fib (Suc 0) = 3" |
      "fib (Suc (Suc n)) = fib n + fib (Suc n)"
    
    (* We try it a little *)
    value "of_nat (fib 4)"
     
    (* And we prove that an iteration of Fibonnaci is working fine! *)
    lemma FibNext: "(CodeFibInside, State inps outs (nMem l r [0, of_nat (fib (Suc n)),0, of_nat (fib n),0] 1)) →*
        ([], State inps outs (nMem l r [0, of_nat (fib (Suc (Suc n))),0, of_nat (fib (Suc n)),0] 1))"
    proof -
      have "∀n na. (of_nat na::8 word) + of_nat n = of_nat (n + na)"
        by auto
      then show ?thesis
        by (metis FibInside fib.simps(3))
    qed

(**************************

  Here are some lemma I did not finished about proving a loop in general works as expected, or some stuff like that

***************************)  
      
(*
lemma DuplicateRight: "(CodeDuplicateRight, State inps outs (nMem l r [c, a, b] 0)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
  apply(auto) (* expand niceMem things *)
  apply(insert twoCopiesOnRight[where inps=inps and outs=outs and l=l and r=r and c=c])
    
    
    
lemma DuplicateRight: "(CodeDuplicateRight, State inps outs (nMem l r [c, a, b] 0)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
    apply(auto) (* expand niceMem things *)
    proof -
  have "([MoveLeft, MoveLeft], State inps outs (nMem l r [b+c, a+c, 0] 2)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
    apply(auto)
    by (meson UnfoldLeftSmth link_two_smallsteps)
  have "(CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (nMem l r [0, a+c, b+c] 2)) →* ([], State inps outs  (nMem l r [b+c, a+c, 0] 2))"
    apply(auto)
    apply(insert moveTwoLeft[where inps=inps and outs=outs and l=l and r=r and a="a+c" and b="0" and c="b+c"])
    apply(drule star_seq[where x="[MoveLeft, MoveLeft]"])
    apply(auto)
      
      
  have "(CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (nMem l r [0, a+c, b+c] 2)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
    apply(auto)
    apply(insert moveTwoLeft[where inps=inps and outs=outs and l=l and r=r and a="a+c" and b="0" and c="b+c"])
    apply(drule star_seq[where x="[MoveLeft, MoveLeft]"])
    apply(auto)
      
      
  have "([MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (nMem l r [0, a+c, b+c] 0)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
    apply(auto)
    sledgehadxmmer [remote_vampire, timeout=120]
  have "(CodeTwoCopiesOnRight@[MoveRight, MoveRight]@CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (nMem l r [c, a, b] 0)) →* ([], State inps outs (nMem l r [b+c, a+c, 0] 0))"
    apply(auto)
    sledgehamxdmer [remote_vampire, timeout=120]
  then show ?thesis
    by simp
qed

  *)
  
(*
lemma DuplicateRight: "(CodeDuplicateRight, State inps outs (Mem l c (a#b#r))) →* ([], State inps outs (Mem l (b+c) (a#0#r)))"
    proof -
  have "([MoveLeft, MoveLeft], State inps outs (Mem (a # (b+c) # l) 0 r)) →* ([], State inps outs (Mem l (b+c) (a # 0 # r)))"
    by (meson UnfoldLeftSmth link_two_smallsteps)
  then have "(CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (Mem (a # b # l) c r)) →* ([], State inps outs (Mem l (b+c) (a # 0 # r)))"
    proof -
      have "∀w wa ws is wsa wsb wb wsc. (CodeMoveTwoLeft @ is, State wsc ws (Mem (wb # wa # wsb) w wsa)) →* ([] @ is, State wsc ws (Mem (wb # (wa + w) # wsb) 0 wsa))"
        using CodeMoveTwoLeft_def moveTwoLeft star_seq by presburger
      then have "(CodeMoveTwoLeft @ [MoveLeft, MoveLeft], State inps outs (Mem (a # b # l) c r)) →* ([MoveLeft, MoveLeft], State inps outs (Mem (a # (b + c) # l) 0 r))"
        by simp
      then show ?thesis
        by (meson ‹([MoveLeft, MoveLeft], State inps outs (Mem (a # (b + c) # l) 0 r)) →* ([], State inps outs (Mem l (b + c) (a # 0 # r)))› link_star_star)
    qed
  then have "(MoveRight#MoveRight#CodeMoveTwoLeft@[MoveLeft, MoveLeft], State inps outs (Mem (a # b # l) c r)) →* ([], State inps outs (Mem l (b+c) (a # 0 # r)))"
    by (simxp add:add.commute,metis (full_types) UnfoldDecr add_diff_cancel_left' link_smallstep_star)
  then show ?thesis
    by simp
qed
*)
  
  
  
  
  
  (*
fun safeTail :: "'a list ⇒ 'a list" where
  "safeTail [] = []" | "safeTail (h#t) = t"
fun safeHead :: "byte list ⇒ byte" where
  "safeHead [] = 0" | "safeHead (h#t) = h"
fun nTail :: "'a list ⇒ nat ⇒ 'a list" where (* delete n first items *)
  nTail0:"nTail l 0 = l" |
  nTail1:"nTail [] n = []" |
  "nTail (a#t) (Suc n) = nTail t n"
fun nHead :: "byte list ⇒ nat ⇒ byte list" where
  "nHead l 0 = []" |
  "nHead [] (Suc n) = 0 # (nHead [] n)" |
  "nHead (a#t) (Suc n) = a # nHead t n"
fun nthHead :: "byte list ⇒ nat ⇒ byte" where
  "nthHead l 0 = safeHead l" |
  "nthHead l (Suc n) = safeHead (nTail l n)"

fun repeatInstruction :: "'a ⇒ nat ⇒ 'a list" where
  "repeatInstruction a 0 = []" |
  "repeatInstruction a (Suc n) = a # (repeatInstruction a n)"
  
lemma UnpackRight : "repeatInstruction MoveRight (Suc n) = (repeatInstruction MoveRight n) @ [MoveRight]"
  by(induction n, auto)
  
lemma MoveNRight_sub:"([MoveRight], State inps outs (Mem (nHead (v # r) n @ l) (nthHead (v # r) n) (nTail r n)))
    → ([], State inps outs (Mem (v # nHead r n @ l) (safeHead (nTail (v # r) n)) (nTail r (Suc n))))"
  apply(cases r, auto)
   apply(thin_tac "r=[]")
    sorry

lemma MoveNRight: "
                  (repeatInstruction MoveRight n, State inps outs (Mem l v r)) →*
                 ([], State inps outs (Mem ((nHead (v # r) n)@l) (nthHead (v # r) n) (nTail r n)))"
  apply(induction n, simp)
  apply(simp only:UnpackRight)
  apply(drule star_seq [where x="[MoveRight]"], auto)
    sorry
  *)
(*
lemma emptySame:"([], s) →* ([], s') ⟹ s=s'"
	sorry
		
  
lemma fuck:"([Loop (Decr # X)], State inps outs (Mem l c r)) 
    	→ (Decr # X @ [Loop (Decr # X)], State inps outs (Mem l c r)) ⟹
    (Decr # X @ [Loop (Decr # X)], State inps outs (Mem l c r)) 
    	→ (X @ [Loop (Decr # X)], State inps outs (Mem l (c - 1) r)) ⟹ ([Loop (Decr # X)], State inps outs (Mem l c r)) →* (X @ [Loop (Decr # X)], State inps outs (Mem l (c - 1) r))"
  by (simp add: link_two_smallsteps)
  
  
lemma genericLoopsSST: "
		∀ v . ((X, State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')))
⟹ c≠0 ⟹
		([Loop (Decr#X)], State inps outs (Mem l c r)) →* ([Loop (Decr#X)], State inps' outs' (Mem l' (c-1) r'))"
		apply(drule LoopT[where inside="Decr#X" and inps="inps" and outs="outs" and l=l and r=r])
	apply(insert UnfoldDecr[where li="X@[Loop (Decr#X)]" and inps="inps" and outs="outs" and l=l and r=r and c=c])
	apply(simp)
	apply(drule fuck, simp)
	apply(drule spec[where x="c-1"])
		apply(drule star_seq[where x="[Loop (Decr#X)]"]) back
	apply(auto)
	apply(erule link_star_star)		
	apply(auto)
	done

lemma genericLoopsSST_G: "
		∀ v . ((X, State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')))
⟹ c≠0 ⟹
	(X@[Loop (Decr#X)], State inps outs (Mem l (c-1) r)) →* ([Loop (Decr#X)], State inps' outs' (Mem l' (c-1) r')) "
	using star_seq by fastforce
	
lemma niceMeansNice:"∀ v . ((X, State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')))
⟹ ∀ v . ((repeatList X (unat c), State inps outs (Mem l v r)) →* ([], State inps'' outs'' (Mem l'' v r'')))"
	sorry
lemma genericLoops: "
		∀ v . ((repeatList X (unat c), State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')))
⟹
		([Loop (Decr#X)], State inps outs (Mem l c r)) →* ((repeatList X (unat c))@[], State inps' outs' (Mem l' 0 r'))"
	sorry
		
lemma break : ""

lemma CopyOperation: "(([MoveRight, Incr, MoveLeft], State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')))"
	apply(cases r)
		apply(subgoal_tac "([MoveRight], State inps outs (Mem l v r)) → ([], State inps outs (Mem l v r))")
		apply(drule star.refl)
lemma SimpleCopy: ""
		
	
	  
	
	*)
	
	
		(*

lemma xxxxxx:"(Decr # inside @ [Loop (Decr # inside)], State inps outs (Mem l (c + 1) r)) → (inside @ [Loop (Decr # inside)], State inps outs (Mem l c r)) ⟹
    (inside @ [Loop (Decr # inside)], State inps outs (Mem l c r)) →* ([Loop (Decr # inside)], State inps'' outs'' (Mem l'' c r'')) ⟹
	(Decr # inside @ [Loop (Decr # inside)], State inps outs (Mem l (c + 1) r)) →* ([Loop (Decr # inside)], State inps'' outs'' (Mem l'' c r''))"
	by (meson star.simps)
		
		lemma hohoho:"([Loop (Decr # inside)], State inps outs (Mem l (1 + c) r)) → (Decr # inside @ [Loop (Decr # inside)], State inps outs (Mem l (1 + c) r)) ⟹
    (Decr # inside @ [Loop (Decr # inside)], State inps outs (Mem l (c + 1) r)) → (inside @ [Loop (Decr # inside)], State inps outs (Mem l c r))"
    	by (metis UnfoldDecr add.commute add_diff_cancel_left')
    	
lemma heyhey:(*"1 + c ≠ 0 ⟹
         (∀v. (repeatList inside (unat c), State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')) ⟹
          ([Loop (Decr # inside)], State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' 0 r'))) ⟹
         ∀v. (inside, State inps outs (Mem l v r)) →* ([], State inps'' outs'' (Mem l'' v r'')) ⟹
         ∀v. (repeatList inside (unat (1 + c)), State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r')) ⟹
         ([Loop (Decr # inside)], State inps outs (Mem l (1 + c) r)) →* ([], State inps' outs' (Mem l' 0 r'))"*)
  "1 + c ≠ 0 ⟹
         ((repeatList inside (unat c), State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' c r')) ⟹
          ([Loop (Decr # inside)], State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' 0 r'))) ⟹
         ∀v. (inside, State inps' outs' (Mem l' v r')) →* ([], State inps'' outs'' (Mem l'' v r'')) ⟹
         (repeatList inside (unat (1 + c)), State inps outs (Mem l (1 + c) r)) →* ([], State inps' outs' (Mem l' (1 + c) r')) ⟹
         ([Loop (Decr # inside)], State inps outs (Mem l (1 + c) r)) →* ([], State inps' outs' (Mem l' 0 r'))"
       apply(drule LoopT[where inside="Decr#inside" and inps=inps and outs=outs and l=l and r=r])
  apply(auto)
	apply(insert UnfoldDecr[where li="inside@[Loop (Decr#inside)]" and inps=inps and outs=outs and l=l and r=r and c="c+1"])
	apply(auto)
	apply(drule spec[where x="c"])
		(*apply(thin_tac "∀v. (repeatList inside (unat (1 + c)), State inps outs (Mem l v r)) →* ([], State inps' outs' (Mem l' v r'))")*)
	apply(frule hohoho) 
	apply(auto)
	apply(drule star_seq[where x="[Loop (Decr#inside)]"])
	apply(auto)
	apply(drule xxxxxx[where outs''="outs''" and inps''="inps''" and l''="l''" and r''="r''"]) 
		apply(auto)
		sorry
done
		
lemma genericLoop:"
		∀v. (inside, State inps' outs' (Mem l' v r')) →* ([], State inps'' outs'' (Mem l'' v r''))
⟹
		(repeatList inside (unat c), State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' c r'))
⟹
		 ([Loop (Decr # inside)], (State inps outs (Mem l c r)))
				 →*
     ([], State inps' outs' (Mem l' 0 r'))
"
	apply(induction c)
	 apply(auto)
	 apply((drule spec[where x="c"])+)
	 apply(drule emptySame)
	  apply(auto)
	 apply(simp add:LoopF)
	 apply(simp add:heyhey)
*)
	(*
lemma TEST:"1 + c ≠ 0 ⟹
         ((repeatList inside (unat c), State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' c r')) ⟹
          ([Loop (Decr # inside)], State inps outs (Mem l c r)) →* ([], State inps' outs' (Mem l' 0 r'))) ⟹
         (repeatList inside (unat (1 + c)), State inps outs (Mem l (1 + c) r)) →* ([], State inps' outs' (Mem l' (1 + c) r')) ⟹
         ([Loop (Decr # inside)], State inps outs (Mem l (1 + c) r)) →* ([], State inps' outs' (Mem l' 0 r')) "
  apply(drule LoopT[where inside="Decr#inside" and inps=inps and outs=outs and l=l and r=r])
  apply(auto)
	apply(insert UnfoldDecr[where li="[Loop (Decr#inside)]" and inps=inps and outs=outs and l=l and r=r and c="c+1"])
		 apply(auto)
	apply(drule spec[where x="inps0"])
  	apply(drule spec[where x="outs0"])
  	apply(drule spec[where x="l0"])
  apply(drule spec[where x="r0"])
  	apply(erule mp)
	  apply(subgoal_tac "(repeatList inside (unat c), State inps outs (Mem l c r)) → (repeatList inside (unat (1 + c)), State inps outs (Mem l (1 + c) r))")
done

	
lemma genericLoop:"
				(repeatList inside (unat c), (State inps outs (Mem l c r))) →* ([], (State inps' outs' (Mem l' c r'))) (* code inside do not touch c *)
			⟹
				 ([Loop (Decr # inside)], (State inps outs (Mem l c r)))
				 →*
         ([], State inps' outs' (Mem l' 0 r'))"
  apply(induction c)
	 apply(auto)
	 apply(drule emptySame)
	 apply(auto)
	 apply(simp add:LoopF)
	  apply(simp add:TEST)
	  
	done

(*lemma oneCopyOnRight:"([Loop [Decr, MoveRight, Incr, MoveLeft]], (State inps outs (Mem l c (n#r)))) →* ([], State inps outs (Mem l 0 ((n+c)#r)))"
	apply(induction c)
	 apply(simp add:LoopF)
	  
	done*)
		
		*)

end
