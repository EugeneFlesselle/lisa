package lisa.maths

import lisa.fol.FOL
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.*

import scala.collection.mutable.Set as mSet
import scala.collection.mutable.Map as mMap

object OrthologicWithAxioms extends lisa.Main:

  /** ORTHOLATTICE SYMBOLS **/

  // ortholattice elements
  val x, y, z = variable

  val <= = ConstantPredicateLabel("<=", 2)
  val u = ConstantFunctionLabel("u", 2)
  val n = ConstantFunctionLabel("n", 2)
  val not = ConstantFunctionLabel("¬", 1)

  val `0` = Constant("0")
  val `1` = Constant("1")

  Set(<=, u, n, not, `0`, `1`) foreach addSymbol

  extension (left: Term)
    def <=(right: Term): Formula = AppliedPredicate(OrthologicWithAxioms.<=, Seq(left, right))
    def u(right: Term): Term = AppliedFunction(OrthologicWithAxioms.u, Seq(left, right))
    def n(right: Term): Term = AppliedFunction(OrthologicWithAxioms.n, Seq(left, right))


  /** ORTHOLATTICE AXIOMS **/

  val p1 = Axiom(x <= x)
  val p2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z))
  val p3a = Axiom(`0` <= x)
  val p3b = Axiom(x <= `1`)
  val p4a = Axiom((x n y) <= x)
  val p4b = Axiom(x <= (x u y))
  val p5a = Axiom((x n y) <= y)
  val p5b = Axiom(y <= (x u y))
  val p6a = Axiom((x <= y) /\ (x <= z) ==> (x <= (y n z)))
  val p6b = Axiom((x <= z) /\ (y <= z) ==> ((x u y) <= z))
  val p7a = Axiom(x <= not(not(x)))
  val p7b = Axiom(not(not(x)) <= x)
  val p8 = Axiom((x <= y) ==> (not(y) <= not(x)))
  val p9a = Axiom((x n not(x)) <= `0`)
  val p9b = Axiom(`1` <= (x u not(x))) // NOTE admissible from other axioms


  val p3c = Lemma(not(`1`) <= x) {
    have(not(x) <= `1`) by Restate.from(p3b of (x := not(x)))
    have(not(`1`) <= not(not(x))) by Tautology.from(lastStep, p8 of (x := not(x), y := `1`))
    have(thesis) by Tautology.from(lastStep, p7b, p2 of (x := not(`1`), y := not(not(x)), z := x))
  }

  val notnot = Lemma((x <= not(not(y))) <=> (x <= y)) {
    val s1 = have((x <= not(not(y))) ==> (x <= y)) by Tautology.from(p7b of (x := y), p2 of (y := not(not(y)), z := y))
    val s2 = have((x <= y) ==> (x <= not(not(y)))) by Tautology.from(p7a of (x := y), p2 of (z := not(not(y))))
    have(thesis) by Tautology.from(s1, s2)
  }


  /** ORTHOLOGIC SEQUENT ENCODING **/

  // annotated formulas
  val gamma, delta = variable

  val L = ConstantFunctionLabel("L", 1) // Annotate term as formula on left
  val R = ConstantFunctionLabel("R", 1) // Annotate term as formula on right
  val N = Constant("N") // A placeholder for no formula

  val S = ConstantPredicateLabel("S", 2) // OL Sequent of 2 annotated formulas
  val I = ConstantFunctionLabel("I", 1) // interpretation of annotated formula

  Set(L, R, N, S, I) foreach addSymbol

  def S1(t: Term): Formula = S(t, N) \/ S(N, t)
  def NI(t: Term): Term = not(I(t))

  val IS = Axiom(S(gamma, delta) <=> (I(gamma) <= NI(delta)))
  val IL = Axiom(I(L(x)) === x)
  val IR = Axiom(I(R(x)) === not(x))
  val IN = Axiom(I(N) === `1`)


  val commutS = Theorem(S(gamma, delta) |- S(delta, gamma)) {
    assume(S(gamma, delta))
    val (g, d) = (I(gamma), I(delta))
    have(g <= not(d)) by Tautology.from(IS)
    val s1 = have(not(not(d)) <= not(g)) by Tautology.from(lastStep, p8 of(x := g, y := not(d)))
    val s2 = have(d <= not(not(d))) by Tautology.from(p7a of (x := d))
    have(d <= not(g)) by Tautology.from(s1, s2, p2 of(x := d, y := not(not(d)), z := not(g)))
    have(thesis) by Tautology.from(lastStep, IS of(gamma := delta, delta := gamma))
  }

  val SFR = Theorem(S(gamma, R(y)) <=> (I(gamma) <= y)) {
    have(S(gamma, R(y)) <=> (I(gamma) <= NI(R(y)))) by Tautology.from(IS of(delta := R(y)))
    thenHave(S(gamma, R(y)) <=> (I(gamma) <= not(not(y)))) by Substitution.ApplyRules(IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := I(gamma)))
  }

  val SLF = Theorem(S(L(x), delta) <=> (x <= NI(delta))) {
    have(S(L(x), delta) <=> (I(L(x)) <= NI(delta))) by Tautology.from(IS of(gamma := L(x)))
    thenHave(thesis) by Substitution.ApplyRules(IL)
  }

  val SLR = Theorem(S(L(x), R(y)) <=> (x <= y)) {
    have(S(L(x), R(y)) <=> (I(L(x)) <= NI(R(y)))) by Restate.from(IS of (gamma := L(x), delta := R(y)))
    thenHave(S(L(x), R(y)) <=> (x <= not(not(y)))) by Substitution.ApplyRules(IL, IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot)
  }

  val SLL = Theorem(S(L(x), L(y)) <=> (x <= not(y))) {
    have(S(L(x), L(y)) <=> (I(L(x)) <= NI(L(y)))) by Restate.from(IS of (gamma := L(x), delta := L(y)))
    thenHave(thesis) by Substitution.ApplyRules(IL, IL of (x := y))
  }

  val SRR = Theorem(S(R(x), R(y)) <=> (not(x) <= y)) {
    have(S(R(x), R(y)) <=> (I(R(x)) <= NI(R(y)))) by Restate.from(IS of (gamma := R(x), delta := R(y)))
    thenHave(S(R(x), R(y)) <=> (not(x) <= not(not(y)))) by Substitution.ApplyRules(IR, IR of (x := y))
    have(thesis) by Tautology.from(lastStep, notnot of (x := not(x)))
  }

  val SLN = Theorem(S(L(x), N) <=> (x <= `0`)) {
    have(S(L(x), N) <=> (x <= NI(N))) by Restate.from(SLF of (delta := N))
    thenHave(S(L(x), N) <=> (x <= not(`1`))) by Substitution.ApplyRules(IN)
    have(thesis) by Tautology.from(lastStep,
      p3c of (x := `0`), p2 of (y := not(`1`), z := `0`),
      p3a of (x := not(`1`)), p2 of (y := `0`, z := not(`1`)),
    )
  }

  val SNR = Theorem(S(N, R(y)) <=> (`1` <= y)) {
    have(S(N, R(y)) <=> (I(N) <= y)) by Restate.from(SFR of (gamma := N))
    thenHave(thesis) by Substitution.ApplyRules(IN)
  }

  val SNN = Theorem(S(N, N) <=> (`1` <= `0`)) {
    val s1 = have((`1` <= not(`1`)) ==> (`1` <= `0`)) by Tautology.from(p3c of (x := `0`), p2 of (x := `1`, y := not(`1`), z := `0`))
    val s2 = have((`1` <= `0`) ==> (`1` <= not(`1`))) by Tautology.from(p3a of (x := not(`1`)), p2 of (x := `1`, y := `0`, z := not(`1`)))
    have(S(N, N) <=> (`1` <= not(`1`))) by Substitution.ApplyRules(IN)(IS of (gamma := N, delta := N))
    have(thesis) by Tautology.from(lastStep, s1, s2)
  }


  /** DERIVATION RULES **/

  val hyp = Theorem(S(L(x), R(x))) {
    have(thesis) by Tautology.from(p1, SLR of (y := x))
  }

  val cut = Theorem(S(gamma, R(x)) /\ S(L(x), delta) |- S(gamma, delta)) {
    assume(S(gamma, R(x)) /\ S(L(x), delta))
    val s1 = have(I(gamma) <= x) by Tautology.from(SFR of (y := x))
    val s2 = have(x <= NI(delta)) by Tautology.from(SLF)
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := x, z := NI(delta)), IS)
  }

  val weaken = Theorem(S(gamma, N) |- S(gamma, delta)) {
    assume(S1(gamma))
    have(I(gamma) <= NI(N)) by Tautology.from(commutS of (gamma := N, delta := gamma), IS of (delta := N))
    val s1 = thenHave(I(gamma) <= not(`1`)) by Substitution.ApplyRules(IN)
    val s2 = have(not(`1`) <= NI(delta)) by Tautology.from(p3c of (x := NI(delta)))
    have(thesis) by Tautology.from(s1, s2, p2 of (x := I(gamma), y := not(`1`), z := NI(delta)), IS)
  }

  val contraction = Theorem(S(gamma, gamma) |- S(gamma, N)) {
    assume(S(gamma, gamma))
    val G = I(gamma)
    have(G <= not(G)) by Tautology.from(IS of (delta := gamma))
    have(G <= (G n not(G))) by Tautology.from(lastStep, p1 of (x := G), p6a of (x := G, y := G, z := not(G)))
    have(G <= `0`) by Tautology.from(lastStep, p9a of (x := G), p2 of (x := G, y := (G n not(G)), z := `0`))
    have(G <= not(`1`)) by Tautology.from(lastStep, p3a of (x := not(`1`)), p2 of (x := G, y := `0`, z := not(`1`)))
    thenHave(I(gamma) <= NI(N)) by Substitution.ApplyRules(IN)
    have(thesis) by Tautology.from(lastStep, IS of (delta := N))
  }

  val leftAnd1 = Theorem(S(L(x), delta) |- S(L(x n y), delta)) {
    have(S(L(x n y), R(x))) by Tautology.from(p4a, SLR of(x := (x n y), y := x))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := L(x n y)))
  }
  val leftAnd2 = Theorem(S(L(y), delta) |- S(L(x n y), delta)) {
    have(S(L(x n y), R(y))) by Tautology.from(p5a, SLR of (x := (x n y)))
    have(thesis) by Tautology.from(lastStep, cut of(gamma := L(x n y), x := y))
  }

  val leftOr = Theorem(S(L(x), delta) /\ S(L(y), delta) |- S(L(x u y), delta)) {
    assume(S(L(x), delta) /\ S(L(y), delta))
    have((x <= NI(delta)) /\ (y <= NI(delta))) by Tautology.from(SLF, SLF of (x := y))
    have((x u y) <= NI(delta)) by Tautology.from(lastStep, p6b of (z := NI(delta)))
    thenHave(I(L(x u y)) <= NI(delta)) by Substitution.ApplyRules(IL)
    have(thesis) by Tautology.from(lastStep, IS of (gamma := L(x u y)))
  }

  val leftNot = Theorem(S(gamma, R(x)) |- S(gamma, L(not(x)))) {
    have(S(L(x), L(not(x)))) by Tautology.from(p7a, SLL of (y := not(x)))
    have(thesis) by Tautology.from(lastStep, cut of (delta := L(not(x))))
  }

  val rightAnd = Theorem(S(gamma, R(x)) /\ S(gamma, R(y)) |- S(gamma, R(x n y))) {
    assume(S(gamma, R(x)) /\ S(gamma, R(y)))
    have((I(gamma) <= x) /\ (I(gamma) <= y)) by Tautology.from(SFR of (y := x), SFR)
    have(I(gamma) <= (x n y)) by Tautology.from(lastStep, p6a of (x := I(gamma), y := x, z := y))
    have(thesis) by Tautology.from(lastStep, SFR of (y := (x n y)))
  }

  val rightOr1 = Theorem(S(gamma, R(x)) |- S(gamma, R(x u y))) {
    have(S(L(x), R(x u y))) by Tautology.from(p4b, SLR of (y := (x u y)))
    have(thesis) by Tautology.from(lastStep, cut of (delta := R(x u y)))
  }
  val rightOr2 = Theorem(S(gamma, R(y)) |- S(gamma, R(x u y))) {
    have(S(L(y), R(x u y))) by Tautology.from(p5b, SLR of(x := y, y := (x u y)))
    have(thesis) by Tautology.from(lastStep, cut of(x := y, delta := R(x u y)))
  }

  val rightNot = Theorem(S(L(x), delta) |- S(R(not(x)), delta)) {
    have(S(R(not(x)), R(x))) by Tautology.from(p7b, SRR of (x := not(x), y := x))
    have(thesis) by Tautology.from(lastStep, cut of (gamma := R(not(x))))
  }


  object RestateWithAxioms extends ProofTactic:
    var log = false

    def apply(using lib: library.type, proof: lib.Proof)
             (bot: Sequent): proof.ProofTacticJudgement = from(bot)

    def from(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =
      if bot.right.size != 1 then
        proof.InvalidProofTactic("Only support goals of the form axioms |- left <= right")
      else bot.right.head match
        case (left <= right) =>

          val left1 = if left == `1` then N else L(left)
          val right1 = if right == `0` then N else R(right)
          
          if bot.left.isEmpty /* no axioms */ then TacticSubproof:
            val s1 = withParameters(Set.empty)(left1, right1)
            have(left <= right) by Tautology.from(
              have(s1),
              SLR of(x := left, y := right),
              SLN of (x := left), SNR of (y := right), SNN
            )
          else

            val axioms: Set[Formula] = bot.left
            val axiomsS: Set[Formula] = axioms.toSet.collect {
              case (`1`  <= `0`   ) => S(N,       N       )
              case (`1`  <= right ) => S(N,       R(right))
              case (left <= `0`   ) => S(L(left), N       )
              case (left <= right ) => S(L(left), R(right))
            }

            val axToAxS = have(axioms |- axiomsS) by Tautology.from(
              axioms.collect {
                case (`1` <= `0`) => SNN
                case (`1` <= r) => SNR of (y := r)
                case (l <= `0`) => SLN of (x := l)
                case (l <= r) => SLR of(x := l, y := r)
              }.toSeq *
            )

            val s1 = withParameters(axiomsS)(left1, right1)

            extension (using proof: lib.Proof)(j: proof.ProofTacticJudgement)
              infix def andThen1(continueProof: (ip: proof.InnerProof) ?=> proof.ProofStep => Unit): proof.ProofTacticJudgement =
                j match
                  case ipt: proof.InvalidProofTactic => ipt
                  case vpt: proof.ValidProofTactic =>
                    val s1 = have(vpt)
                    TacticSubproof(using proof)(continueProof(s1))

            s1 andThen1 { lastStep => // axiomsS |- S(left1, right1)
              val s1 = have(axiomsS |- left <= right) by Tautology.from(lastStep,
                SLR of(x := left, y := right),
                SLN of (x := left), SNR of (y := right), SNN
              )

              have(axioms |- left <= right) by Tautology.from(
                axioms.collect {
                  case (`1` <= `0`) => SNN
                  case (`1` <= r) => SNR of (y := r)
                  case (l <= `0`) => SLN of (x := l)
                  case (l <= r) => SLR of(x := l, y := r)
                }.toSeq :+ s1 *
              )
            }

        case _ => proof.InvalidProofTactic("Only support goals of the form () |- left <= right")


    /**
     * @param axioms of the form S(gamma, delta)
     * @param left a term of form L(x) | N
     * @param right a term of form R(x) | N
     * @return proof tactic judgement for: `axioms` |- S(L(`left`), R(`right`))
     */
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (axiomsS: Set[Formula])(left: Term, right: Term): proof.ProofTacticJudgement =

      val axFormulas: Set[Term] = axiomsS
        .flatMap { case S(gamma1, delta1) => Set(gamma1, delta1) }
        .collect { case L(x) => x case R(x) => x }

      val cache = mMap[(Term, Term), Any]()

      def proved(using proof: lib.Proof)(gamma1: Term, delta1: Term): Boolean =
        prove(gamma1, delta1).isValid

      def prove(using proof: lib.Proof)(gamma1: Term, delta1: Term): proof.ProofTacticJudgement =
        cache.get(gamma1, delta1) match
          case Some(cachedSamePath: proof.ProofTacticJudgement) => cachedSamePath
          case Some(r) if r.isInstanceOf[proof.InvalidProofTactic] =>
            r.asInstanceOf[proof.ProofTacticJudgement]
            // NOTE works to avoid cycles but doesn't reuse a ValidProofTactic with different path
          case _ =>
            cache.addOne((gamma1, delta1), proof.InvalidProofTactic(s"Starting prove($gamma1, $delta1)"))
            val r = proveNoC(gamma1, delta1)
            cache.addOne((gamma1, delta1), r)
            r

      // proove axiomS |- S(gamma, delta) if can
      def proveNoC(using proof: lib.Proof)(gamma1: Term, delta1: Term): proof.ProofTacticJudgement = TacticSubproof:
        val goal: Sequent = axiomsS |- S(gamma1, delta1)
        (gamma1, delta1) match

          // Hyp
          case (L(x1), R(y)) if x1 == y => have(goal) by Weakening(hyp of (x := x1))

          // Ax
          case (gamma1, delta) if axiomsS.contains(S(gamma1, delta1)) =>
            have(goal) by RewriteTrue

          // Weaken
          case (gamma1, delta1) if gamma1 != N && delta1 != N && proved(gamma1, N) =>
            have(goal) by Cut(have(prove(gamma1, N)), weaken of (gamma := gamma1, delta := delta1))

          // Contraction
          case (gamma1, N) if proved(gamma1, gamma1) =>
            have(goal) by Cut(have(prove(gamma1, gamma1)), contraction of (gamma := gamma1))

          // LeftNot
          case (gamma1, L(not(x1))) if proved(gamma1, R(x1)) =>
            have(goal) by Cut(have(prove(gamma1, R(x1))), leftNot of (gamma := gamma1, x := x1))

          // LeftAnd
          case (L(x1 n y1), delta1) if proved(L(x1), delta1) =>
            have(goal) by Cut(have(prove(L(x1), delta1)), leftAnd1 of(x := x1, y := y1, delta := delta1))
          case (L(x1 n y1), delta1) if proved(L(y1), delta1) =>
            have(goal) by Cut(have(prove(L(y1), delta1)), leftAnd2 of(x := x1, y := y1, delta := delta1))

          // LeftOr
          case (L(x1 u y1), delta1) if proved(L(x1), delta1) && proved(L(y1), delta1) =>
            have(axiomsS |- S(L(x1), delta1) /\ S(L(y1), delta1)) by
              RightAnd(have(prove(L(x1), delta1)), have(prove(L(y1), delta1)))
            have(goal) by Cut(lastStep, leftOr of(x := x1, y := y1, delta := delta1))

          // RightNot
          case (R(not(x1)), delta1) if proved(L(x1), delta1) =>
            have(goal) by Cut(have(prove(L(x1), delta1)), rightNot of(delta := delta1, x := x1))

          // RightAnd
          case (gamma1, R(x1 n y1)) if proved(gamma1, R(x1)) && proved(gamma1, R(y1)) =>
            have(axiomsS |- S(gamma1, R(x1)) /\ S(gamma1, R(y1))) by
              RightAnd(have(prove(gamma1, R(x1))), have(prove(gamma1, R(y1))))
            have(goal) by Cut(lastStep, rightAnd of(x := x1, y := y1, gamma := gamma1))

          // RightOr
          case (gamma1, R(x1 u y1)) if proved(gamma1, R(x1)) =>
            have(goal) by Cut(have(prove(gamma1, R(x1))), rightOr1 of (x := x1, y := y1, gamma := gamma1))
          case (gamma1, R(x1 u y1)) if proved(gamma1, R(y1)) =>
            have(goal) by Cut(have(prove(gamma1, R(y1))), rightOr2 of (x := x1, y := y1, gamma := gamma1))

          // AxCut
          case (gamma1, delta1) if axFormulas.exists(x1 => proved(gamma1, R(x1)) && proved(L(x1), delta1)) =>
            LazyList.from(axFormulas)
              .map { x1 => (x1, (prove(gamma1, R(x1)), prove(L(x1), delta1))) }
              .collectFirst { case (x1, (s1, s2)) if s1.isValid && s2.isValid =>
                have(axiomsS |- S(gamma1, R(x1)) /\ S(L(x1), delta1)) by RightAnd(have(s1), have(s2))
                have(goal) by Cut(lastStep, cut of(gamma := gamma1, x := x1, delta := delta1))
              }.get

          // Try by flipping delta1, gamma1
          case (gamma1, delta1) if proved(delta1, gamma1) =>
            have(goal) by Cut(have(prove(delta1, gamma1)), commutS of (gamma := delta1, delta := gamma1))

          case _ => return proof.InvalidProofTactic(s"No rules applied to $gamma1, $delta1")

      end proveNoC

      prove(left, right)
    end withParameters

  end RestateWithAxioms


  val test1 = Theorem(x <= x) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test2a = Theorem((x n (not(x))) <= `0`) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test2 = Theorem(x <= (x u y)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test3 = Theorem((y n x) <= y) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test3b = Theorem((y n x) <= x) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test4 = Theorem((x n y) <= (y u z)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test5 = Theorem(`1` <= x |- not(x) <= `0`) {
    have(thesis) by RestateWithAxioms.apply
  }

  val testPaperExample = Theorem(`1` <= (x n (not(x) u z)) |- `1` <= z) {
    have(thesis) by RestateWithAxioms.apply
  }

  val testP9b = Theorem(`1` <= (x u not(x))) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test10 = Theorem(((x <= y), (y <= z)) |- (x <= z)) {
    have(thesis) by RestateWithAxioms.apply
  }

  val test11 = Theorem((x u y) <= z |- x <= z) {
    have(thesis) by RestateWithAxioms.apply
  }
  

end OrthologicWithAxioms
