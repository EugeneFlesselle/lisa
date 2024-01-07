
import java.util.NoSuchElementException
import scala.collection.mutable.Map as mMap

import lisa.automation.kernel.CommonTactics.Definition
import lisa.fol.FOL as F
import lisa.maths.settheory.SetTheory.*
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicWithAxiomsST extends lisa.Main:

  // ortholattice signature
  val S, T, U = variable
  val <= = variable
  val n, u, not = variable
  val `0`, `1` = variable

  // ortholattice elements
  val v, w, x, y, z = variable

  // needed for subst in defs from maths.SetTheory
  val a, b, c, f, r, t = variable

  // ==============================================================================================
  // ========================================== DSL ===============================================
  // ==============================================================================================

  given zero2term: Conversion[0, Term] with
    inline def apply(x: 0): Term = `0`
  given one2term: Conversion[1, Term] with
    inline def apply(x: 1): Term = `1`

  extension (left: Term)
    inline def <=(right: Term): Formula = pair(left, right) ∈ OrthologicWithAxiomsST.<=
    inline def n(right: Term): Term = app(OrthologicWithAxiomsST.n, pair(left, right))
    inline def u(right: Term): Term = app(OrthologicWithAxiomsST.u, pair(left, right))
    inline def x(right: Term): Term = cartesianProduct(left, right)
    inline def unary_! = app(OrthologicWithAxiomsST.not, left)


  def forallInU(xs: Variable*)(f: Formula): Formula =
    xs.foldRight(f) { (x, g) => ∀(x, x ∈ U ==> g) }

  def inU(xs: Term*): Seq[F.Formula] = xs.map(_ ∈ U)

  extension (xs: Iterable[Term]) def inU: Seq[F.Formula] = xs.map(_ ∈ U).toSeq
  extension (x: Term) def inU: Seq[F.Formula] = Seq(x ∈ U)
  extension [T <: Tuple](t: T)(using eq: Tuple.Union[t.type] <:< Term)
    def inU: Seq[F.Formula] = eq.substituteCo[List](t.toList).map(_ ∈ U)

  
  // ==============================================================================================
  // ================================== ORTHOLATTICE DEFINITION ===================================
  // ==============================================================================================
  
  val p0 = DEF(U, <=, n, u, not, `0`, `1`) --> And(Seq(
    relationBetween(<=, U, U),
    functionFrom(not, U, U), functionFrom(n, U x U, U), functionFrom(u, U x U, U),
    `0` ∈ U, `1` ∈ U
  ))

  val p1 = DEF(U, <=) --> forallInU(x) { x <= x }
  val p2 = DEF(U, <=) --> forallInU(x, y, z) { (x <= y) /\ (y <= z) ==> x <= z }
  val p3a = DEF(U, <=, `0`) --> forallInU(x) { `0` <= x }
  val p3b = DEF(U, <=, `1`) --> forallInU(x) { x <= `1` }
  val p4a = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= x }
  val p5a = DEF(U, <=, n) --> forallInU(x, y) { (x n y) <= y }
  val p4b = DEF(U, <=, u) --> forallInU(x, y) { x <= (x u y) }
  val p5b = DEF(U, <=, u) --> forallInU(x, y) { y <= (x u y) }
  val p6a = DEF(U, <=, n) --> forallInU(x, y, z) { (x <= y) /\ (x <= z) ==> x <= (y n z) }
  val p6b = DEF(U, <=, u) --> forallInU(x, y, z) { (x <= z) /\ (y <= z) ==> (x u y) <= z }
  val p7a = DEF(U, <=, not) --> forallInU(x) { x <= !(!x) }
  val p7b = DEF(U, <=, not) --> forallInU(x) { !(!x) <= x }
  val p8 = DEF(U, <=, not) --> forallInU(x, y) { x <= y ==> !y <= !x }
  val p9a = DEF(U, <=, n, not, `0`) --> forallInU(x) { (x n !x) <= `0` }
  val p9b = DEF(U, <=, u, not, `1`) --> forallInU(x) { `1` <= (x u !x) }

  val ortholattice = DEF(U, <=, n, u, not, `0`, `1`) --> And(Seq(
    p0(U, <=, n, u, not, `0`, `1`),
    p1(U, <=),
    p2(U, <=),
    p3a(U, <=, `0`), p3b(U, <=, `1`),
    p4a(U, <=, n), p4b(U, <=, u),
    p5a(U, <=, n), p5b(U, <=, u),
    p6a(U, <=, n), p6b(U, <=, u),
    p7a(U, <=, not), p7b(U, <=, not),
    p8(U, <=, not),
    p9a(U, <=, n, not, `0`), p9b(U, <=, u, not, `1`)
  ))

  inline def O = ortholattice(U, <=, n, u, not, `0`, `1`)


  // ==============================================================================================
  // =================================== REFORMULATE AXIOMS =======================================
  // ==============================================================================================

  object InstantiatePredicateDefinition extends ProofTactic:

    /**
     * Instantiate universal quantifier of element assumed to be in U.
     *
     * <pre>
     * Γ ⊢ ∀x.(x ∈ U ==> ψ)
     * -------------------------
     * Γ, t ∈ U |- ψ[t/x]
     *
     * </pre>
     */
    object InstantiateForallInU extends ProofTactic:
      def apply(using lib: library.type, proof: lib.Proof)
               (xs: F.Variable*)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
        val premiseSeq = proof.sequentOfFact(premise)

        if premiseSeq.right.size != 1 then
          return proof.InvalidProofTactic("Premise RHS is not a singelton sequent.")
        if !(xs.inU.toSet subsetOf bot.left) then
          return proof.InvalidProofTactic(s"Variables to instantiate are not all assumed to be in $U.")

        TacticSubproof:
          assume(bot.left.toSeq *)
          have(premiseSeq) by Restate.from(premise)

          xs.foreach: x =>
            lastStep.bot.right.head match
              case F.BinderFormula(F.Forall, `x`, F.AppliedConnector(F.Implies, Seq(in(`x`, `U`), phi))) =>
                thenHave(x ∈ U ==> phi) by InstantiateForall(x)
                thenHave(phi) by Rewrite
              case _ => return proof.InvalidProofTactic("Premise did not have expected shape")

          // NOTE this step could also fail but error msg from Rewrite tactic is fine in that case
          thenHave(bot) by Rewrite
    end InstantiateForallInU

    def apply(using lib: library.type, proof: lib.Proof)
             (predicateLabel: ConstantLabel[?])(xs: Variable*)(bot: Sequent): proof.ProofTacticJudgement =

      val predDef = predicateLabel.definition
      val predDefBody: Formula = predDef match
        case predDef: PredicateDefinition[_] => predDef.lambda.body
        case _ => return proof.InvalidProofTactic(s"$predicateLabel is not a PredicateDefinition")

      TacticSubproof:
        have(bot.left |- predDefBody) by Tautology.from(ortholattice.definition, predDef)
        thenHave(bot) by InstantiateForallInU(xs*)

  end InstantiatePredicateDefinition

  val lemmaForP1 = Lemma((O, x ∈ U) |- x <= x):
    have(thesis) by InstantiatePredicateDefinition(p1)(x)

  val lemmaForP2 = Lemma((O, x ∈ U, y ∈ U, z ∈ U) |- (x <= y) /\ (y <= z) ==> x <= z):
    have(thesis) by InstantiatePredicateDefinition(p2)(x, y, z)

  val lemmaForP3A = Lemma((O, x ∈ U) |- 0 <= x):
    have(thesis) by InstantiatePredicateDefinition(p3a)(x)

  val lemmaForP3B = Lemma((O, x ∈ U) |- x <= 1):
    have(thesis) by InstantiatePredicateDefinition(p3b)(x)

  val lemmaForP4A = Lemma(O +: (x, y).inU |- (x n y) <= x):
    have(thesis) by InstantiatePredicateDefinition(p4a)(x, y)

  val lemmaForP4B = Lemma(O +: (x, y).inU |- x <= (x u y)):
    have(thesis) by InstantiatePredicateDefinition(p4b)(x, y)

  val lemmaForP5A = Lemma(O +: (x, y).inU |- (x n y) <= y):
    have(thesis) by InstantiatePredicateDefinition(p5a)(x, y)

  val lemmaForP5B = Lemma(O +: (x, y).inU |- y <= (x u y)):
    have(thesis) by InstantiatePredicateDefinition(p5b)(x, y)

  val lemmaForP6A = Lemma((O, x ∈ U, y ∈ U, z ∈ U, x <= y, x <= z) |- x <= (y n z)):
    have(thesis) by InstantiatePredicateDefinition(p6a)(x, y, z)

  val lemmaForP6B = Lemma((O, x ∈ U, y ∈ U, z ∈ U, x <= z, y <= z) |- (x u y) <= z):
    have(thesis) by InstantiatePredicateDefinition(p6b)(x, y, z)

  val lemmaForP7A = Lemma((O, x ∈ U) |- x <= !(!x)):
    have(thesis) by InstantiatePredicateDefinition(p7a)(x)

  val lemmaForP7B = Lemma((O, x ∈ U) |- !(!x) <= x):
    have(thesis) by InstantiatePredicateDefinition(p7b)(x)

  val lemmaForP8 = Lemma((O, x ∈ U, y ∈ U, x <= y) |- !y <= !x):
    have(thesis) by InstantiatePredicateDefinition(p8)(x, y)

  val lemmaForP9A = Lemma((O, x ∈ U) |- (x n !x) <= 0):
    have(thesis) by InstantiatePredicateDefinition(p9a)(x)

  val lemmaForP9B = Lemma((O, x ∈ U) |- 1 <= (x u !x)):
    have(thesis) by InstantiatePredicateDefinition(p9b)(x)

  // ==============================================================================================
  // ======================================== LEMMAS ==============================================
  // ==============================================================================================

  val appInCodomain = Theorem((functionFrom(f, S, T), x ∈ S) |- app(f, x) ∈ T):
    assume(functionFrom(f, S, T), x ∈ S)

    val functionalOverS = have(functionalOver(f, S)) subproof:
      val s1 = have(f ∈ setOfFunctions(S, T)) by Tautology.from(functionFrom.definition of (x := S, y := T))
      have(∀(t, t ∈ setOfFunctions(S, T) <=> (t ∈ powerSet(S x T) /\ functionalOver(t, S)))) by Definition(setOfFunctions, setOfFunctionsUniqueness)(S, T)
      thenHave(f ∈ setOfFunctions(S, T) <=> (f ∈ powerSet(S x T) /\ functionalOver(f, S))) by InstantiateForall(f)
      have(thesis) by Tautology.from(lastStep, s1)

    val appInRange = have(app(f, x) ∈ relationRange(f)) subproof:
      have(pair(x, app(f, x)) ∈ f) by Tautology.from(functionalOverS, functionalOverApplication of(x := S, a := x, b := app(f, x)))
      val s1 = thenHave(∃(a, pair(a, app(f, x)) ∈ f)) by RightExists
      have(∀(t, t ∈ relationRange(f) <=> ∃(a, pair(a, t) ∈ f))) by Definition(relationRange, relationRangeUniqueness)(f)
      val s2 = thenHave(app(f, x) ∈ relationRange(f) <=> ∃(a, pair(a, app(f, x)) ∈ f)) by InstantiateForall(app(f, x))
      have(thesis) by Tautology.from(s1, s2)

    have(relationRange(f) ⊆ T) by Tautology.from(functionImpliesRangeSubsetOfCodomain of (x := S, y := T))
    thenHave(∀(z, z ∈ relationRange(f) ==> z ∈ T)) by Substitution.ApplyRules(subsetAxiom of (x := relationRange(f), y := T, z := app(f, x)))
    thenHave(app(f, x) ∈ relationRange(f) |- app(f, x) ∈ T) by InstantiateForall(app(f, x))
    have(thesis) by Cut(appInRange, lastStep)
  end appInCodomain

  val joinInU = Corollary((O, (x ∈ U) /\ (y ∈ U)) |- (x u y) ∈ U):
    val step1 = have(O |- functionFrom(u, U x U, U)) by Tautology.from(ortholattice.definition, p0.definition)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- pair(x, y) ∈ (U x U)) by Tautology.from(pairInCartesianProduct of (a := x, b := y, x := U, y := U))
    have(thesis) by Tautology.from(step1, step2, appInCodomain of (f := u, S := (U x U), T := U, x := pair(x, y)))

  val meetInU = Corollary((O, (x ∈ U) /\ (y ∈ U)) |- (x n y) ∈ U):
    val step1 = have(O |- functionFrom(n, U x U, U)) by Tautology.from(ortholattice.definition, p0.definition)
    val step2 = have((x ∈ U) /\ (y ∈ U) |- pair(x, y) ∈ (U x U)) by Tautology.from(pairInCartesianProduct of (a := x, b := y, x := U, y := U))
    have(thesis) by Tautology.from(step1, step2, appInCodomain of (f := n, S := (U x U), T := U, x := pair(x, y)))

  val negationInU = Corollary((O, x ∈ U) |- !x ∈ U):
    have(O |- functionFrom(not, U, U)) by Tautology.from(ortholattice.definition, p0.definition)
    have(thesis) by Tautology.from(lastStep, appInCodomain of (f := not, S := U, T := U))

  val zeroInU = Lemma(O |- 0 ∈ U):
    have(thesis) by Tautology.from(ortholattice.definition, p0.definition)

  val oneInU = Lemma(O |- 1 ∈ U):
    have(thesis) by Tautology.from(ortholattice.definition, p0.definition)


  object Extractors:

    object Singleton:
      def unapply(t: F.Term): Option[F.Term] = t match
        case unorderedPair(x1, x2) if x1 == x2 => Some(x1)
        case _ => None

    object Pair:
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case unorderedPair(unorderedPair(x1, y1), Singleton(x2)) if x1 == x2 => Some((x1, y1))
        case _ => None

    object App:
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case AppliedFunction(`app`, Seq(fun, arg)) => Some((fun, arg))
        case _ => None

    object Leq:
      val leq = OrthologicWithAxiomsST.<=
      def unapply(t: F.Formula): Option[(F.Term, F.Term)] = t match
        case in(Pair(x, y), `leq`) => Some((x, y))
        case _ => None

    object Meet:
      val meet = OrthologicWithAxiomsST.n
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case App(`meet`, Pair(x, y)) => Some((x, y))
        case _ => None

    object Join:
      val join = OrthologicWithAxiomsST.u
      def unapply(t: F.Term): Option[(F.Term, F.Term)] = t match
        case App(`join`, Pair(x, y)) => Some((x, y))
        case _ => None

    object Not:
      def unapply(t: F.Term): Option[F.Term] = t match
        case App(`not`, x) => Some(x)
        case _ => None

  end Extractors

  object AppliedFromU extends ProofTactic:
    import Extractors.*

    // Example: (O, x ∈ U, y ∈ U) |- ((x u y) ∈ U, !x ∈ U)
    def apply(using lib: library.type, proof: lib.Proof)()
             (bot: Sequent): proof.ProofTacticJudgement =
      if !(bot.left contains O) then return proof.InvalidProofTactic(s"LHS doesn't contain $O")

      val assumedInU = bot.left.collect { case in(x1, `U`) => x1 }
      val toProveInU = bot.right.map {
        case in(x1, `U`) => x1
        case other => return proof.InvalidProofTactic(s"RHS contains $other isn't of shape x ∈ $U")
      }
      if toProveInU.isEmpty then return proof.InvalidProofTactic(s"Nothing to prove in U")

      val proofs = toProveInU.map(withParameters(assumedInU))
      val proofSteps = proofs.map(have(_)) // NOTE can fail
      TacticSubproof:
        have(O +: assumedInU.inU |- toProveInU.inU) by RightAnd(proofSteps.toSeq*)
    end apply

    // proves if can: isO +: inU(assumedInU) |- inU(toProveInU)
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (assumedInU: Set[Term])
                      (toProveInU: Term): proof.ProofTacticJudgement =

      object ProofInU:
        def unapply(using proof: lib.Proof)(t1: Term): Option[proof.ProofStep] =
          prove(t1) match
            case vpt: proof.ValidProofTactic => Some(proof.newProofStep(vpt))
            case ipt: proof.InvalidProofTactic => None

      def prove(using proof: lib.Proof)(t: Term): proof.ProofTacticJudgement = TacticSubproof:
        assume(O +: assumedInU.inU *)
        t match

          case `0` => have(0 ∈ U) by Weakening(zeroInU)
          case `1` => have(1 ∈ U) by Weakening(oneInU)

          case x1 if assumedInU(x1) => have(x1 ∈ U) by RewriteTrue

          case Not(x1 @ ProofInU(x1InU)) =>
            have(!x1 ∈ U) by Cut(x1InU, negationInU of (x := x1))

          case Meet(x1 @ ProofInU(x1InU), x2 @ ProofInU(x2InU)) =>
            have(x1 ∈ U /\ x2 ∈ U) by RightAnd(x1InU, x2InU)
            have((x1 n x2) ∈ U) by Cut(lastStep, meetInU of (x := x1, y := x2))

          case Join(x1 @ ProofInU(x1InU), x2 @ ProofInU(x2InU)) =>
            have(x1 ∈ U /\ x2 ∈ U) by RightAnd(x1InU, x2InU)
            have((x1 u x2) ∈ U) by Cut(lastStep, joinInU of(x := x1, y := x2))

          case other => return proof.InvalidProofTactic(s"Could not prove $other ∈ $U")

      prove(toProveInU)
    end withParameters

    // discharges toDischarge.inU from premise
    def dicharge(using lib: library.type, proof: lib.Proof)
                (toDischarge: Term*)(premise: proof.Fact): proof.ProofTacticJudgement =
      val premiseSeq = proof.sequentOfFact(premise)
      if !(premiseSeq.left contains O) then return proof.InvalidProofTactic(s"LHS doesn't contain $O")

      val assumedInU = premiseSeq.left.collect { case in(x1, `U`) => x1 } -- toDischarge
      TacticSubproof:
        val proofsInU = toDischarge.map(O +: assumedInU.inU |- inU(_)).map(AppliedFromU()).map(have(_))
        have(premiseSeq) by Restate.from(premise)
        if toDischarge.nonEmpty then andThen(Discharge(proofsInU *))

  end AppliedFromU

  // ==============================================================================================
  // ============================================ RULES ===========================================
  // ==============================================================================================

  val hyp = Theorem((O, x ∈ U) |- x <= x):
    have(thesis) by Restate.from(lemmaForP1)

  val cut = Theorem(O +: (x, y, z).inU :+ (x <= y) /\ (y <= z) |- (x <= z)) :
    have(thesis) by Restate.from(lemmaForP2)

  val weaken1 = Theorem(O +: (x, y).inU :+ (x <= 0) |- x <= y):
    have(thesis +<< (0 ∈ U)) by Tautology.from(lemmaForP3A of (x := y), lemmaForP2 of (y := 0, z := y))
    andThen(AppliedFromU.dicharge(0))

  val weaken2 = Theorem(O +: (x, y).inU :+ (1 <= y) |- x <= y) :
    have(thesis +<< (1 ∈ U)) by Tautology.from(lemmaForP3B, lemmaForP2 of(y := 1, z := y))
    andThen(AppliedFromU.dicharge(1))

  val contraction1 = Theorem((O, x ∈ U, x <= !x) |- x <= 0):
    assume(O, x ∈ U)
    have((!x ∈ U, x <= !x) |- x <= (x n !x)) by Tautology.from(lemmaForP6A of (y := x, z := !x), lemmaForP1)
    have((!x, (x n !x), `0`).inU :+ (x <= !x) |- x <= 0) by Tautology.from(lastStep, lemmaForP9A, lemmaForP2 of (y := (x n !x), z := 0))
    andThen(AppliedFromU.dicharge(!x, (x n !x), 0))

  val contraction2 = Theorem((O, x ∈ U, !x <= x) |- 1 <= x):
    assume(O, x ∈ U)
    have((!x ∈ U, !x <= x) |- (x u !x) <= x) by Tautology.from(lemmaForP6B of (y := !x, z := x), lemmaForP1)
    have((!x, (x u !x), `1`).inU :+ (!x <= x) |- 1 <= x) by Tautology.from(lastStep, lemmaForP9B, lemmaForP2 of (x := 1, y := (x u !x), z := x))
    andThen(AppliedFromU.dicharge(!x, (x u !x), 1))

  val leftAnd1 = Theorem(O +: (x, y, z).inU :+ (x <= z) |- (x n y) <= z):
    assume(O +: (x, y, z).inU *)
    have((x n y) <= x) by Tautology.from(lemmaForP4A)
    have(thesis +<< ((x n y) ∈ U)) by Tautology.from(lastStep, lemmaForP2 of (x := (x n y), y := x))
    andThen(AppliedFromU.dicharge(x n y))

  val leftAnd2 = Theorem(O +: (x, y, z).inU :+ (y <= z) |- (x n y) <= z) :
    assume(O +: (x, y, z).inU *)
    have((x n y) <= y) by Tautology.from(lemmaForP5A)
    have(thesis +<< ((x n y) ∈ U)) by Tautology.from(lastStep, lemmaForP2 of(x := (x n y)))
    andThen(AppliedFromU.dicharge(x n y))

  val leftOr = Theorem(O +: (x, y, z).inU :+ (x <= z) /\ (y <= z) |- (x u y) <= z) :
    have(thesis) by Tautology.from(lemmaForP6B)

  val rightAnd = Theorem(O +: (x, y, z).inU :+ (x <= y) /\ (x <= z) |- x <= (y n z)):
    have(thesis) by Tautology.from(lemmaForP6A)

  val rightOr1 = Theorem(O +: (x, y, z).inU :+ (x <= y) |- x <= (y u z)) :
    assume(O +: (x, y, z).inU *)
    have(y <= (y u z)) by Tautology.from(lemmaForP4B of (x := y, y := z))
    have(thesis +<< (y u z) ∈ U) by Tautology.from(lastStep, lemmaForP2 of (z := (y u z)))
    andThen(AppliedFromU.dicharge(y u z))

  val rightOr2 = Theorem(O +: (x, y, z).inU :+ (x <= z) |- x <= (y u z)) :
    assume(O +: (x, y, z).inU *)
    have(z <= (y u z)) by Tautology.from(lemmaForP5B of(x := y, y := z))
    have(thesis +<< (y u z) ∈ U) by Tautology.from(lastStep, lemmaForP2 of (y := z, z := (y u z)))
    andThen(AppliedFromU.dicharge(y u z))

  val commutRL = Theorem(O +: (x, y).inU :+ (x <= y) |- !y <= !x):
    have(thesis) by Tautology.from(lemmaForP8)

  val commutLL = Theorem(O +: (x, y).inU :+ (x <= !y) |- y <= !x) :
    assume(O +: (x, y).inU *)
    have(inU(!y) :+ (x <= !y) |- !(!y) <= !x) by Tautology.from(lemmaForP8 of (y := !y))
    have((!y, !(!y), !x).inU :+ (x <= !y) |- y <= !x) by Tautology.from(lastStep, lemmaForP7A of (x := y), lemmaForP2 of (x := y, y := !(!y), z := !x))
    andThen(AppliedFromU.dicharge(!y, !(!y), !x))

  val commutRR = Theorem(O +: (x, y).inU :+ (!x <= y) |- !y <= x) :
    assume(O +: (x, y).inU *)
    have(inU(!x) :+ (!x <= y) |- !y <= !(!x)) by Tautology.from(lemmaForP8 of (x := !x))
    have((!x, !(!x), !y).inU :+ (!x <= y) |- !y <= x) by Tautology.from(lastStep, lemmaForP7B, lemmaForP2 of(x := !y, y := !(!x), z := x))
    andThen(AppliedFromU.dicharge(!x, !(!x), !y))


  object RestateWithAxioms extends ProofTactic:
    import Extractors.*

    var log = false

    def apply(using lib: library.type, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement =
      if !(bot.left contains O) then
        proof.InvalidProofTactic(s"Only support goals of the with $O as assumption.")
      else bot.right.toSeq match
        case Seq(Leq(left, right)) =>
          val termsInU = bot.left.collect { case in(x, `U`) => x }
          val axioms = bot.left.collect { case ax @ Leq(_, _) => ax }
          withParameters(termsInU, axioms)(left, right)
        case _ => proof.InvalidProofTactic("Only support goals with RHS of the form left <= right")

    end apply

    // O +: axioms ++ assumedInU.inU |- left <= right
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (assumedInU: Set[Term], axioms: Set[Formula])
                      (left: Term, right: Term): proof.ProofTacticJudgement =

      val assumptions: Seq[Formula] = O +: assumedInU.inU concat axioms
      val axFormulas: Set[Term] = axioms.collect { case Leq(l, r) => Set(l, r) }.flatten.filterNot(Set(0, 1))

      // An annotated formula is either a formula wrapped in L for left or in R for right, or N for no formula
      enum AnnotatedF:
        case L(t: F.Term) 
        case R(t: F.Term)
        case N

        def onLeft: Term = this match { case L(t) => t case R(t) => !t case N => `1` }
        def onRight: Term = this match { case L(t) => !t case R(t) => t case N => `0` }
      import AnnotatedF.*

      val cache = mMap[(AnnotatedF, AnnotatedF), Any]()
      var ident = 0

      def prove(using proof: lib.Proof)(gamma: AnnotatedF, delta: AnnotatedF): proof.ProofTacticJudgement =
        cache.get(gamma, delta) match
          case Some(cachedSamePath: proof.ProofTacticJudgement) =>
            cachedSamePath
          case Some(r) if r.isInstanceOf[proof.InvalidProofTactic] =>
            r.asInstanceOf[proof.ProofTacticJudgement]
            // NOTE works to avoid cycles but doesn't reuse a ValidProofTactic with a different path
          case _ =>
            if log then println(" " * ident + s"== starting prove($gamma, $delta)")
            ident += 1

            cache.addOne((gamma, delta), proof.InvalidProofTactic(s"Starting prove($gamma, $delta)"))
            val res: proof.ProofTacticJudgement = proveNotCached(gamma, delta)
            cache.addOne((gamma, delta), res)

            ident -= 1
            if log then println(" " * ident + s"== ending prove($gamma, $delta) with ${res.isValid}")
            res
      end prove

      def proveNotCached(using proof: lib.Proof)(gamma: AnnotatedF, delta: AnnotatedF): proof.ProofTacticJudgement = TacticSubproof:
        assume(assumptions*)

        val (gammaF, deltaF) = (gamma.onLeft, delta.onRight)

        // similar to have, bu used as a pattern guard
        def had(gamma: AnnotatedF, delta: AnnotatedF): Boolean =
          val judjement = prove(gamma, delta)
          if judjement.isValid then have(judjement)
          judjement.isValid

        def hadBoth(gamma1: AnnotatedF, delta1: AnnotatedF)(gamma2: AnnotatedF, delta2: AnnotatedF): Boolean =
          val (j1, j2) = (prove(gamma1, delta1), prove(gamma2, delta2))
          if !(j1.isValid && j2.isValid) then false
          else
            val (s1, s2) = (have(j1), have(j2))
            have(s1.bot.left ++ s2.bot.left |- s1.bot.right.head /\ s2.bot.right.head) by RightAnd(s1, s2)
            true

        // have(... |- gammaF <= deltaF) by Cut(lastStep, fact of insts)
        def cutLastStep(fact: proof.Fact)(insts: (Variable, Term)*) =
          val instantiatedFact = fact.of(insts.map(SubstPair(_, _))*)
          val cutFormula = lastStep.bot.right.head
          val bot = lastStep.bot.left ++ insts.map(_._2).inU |- gammaF <= deltaF
          have(bot) by Cut.withParameters(cutFormula)(lastStep, instantiatedFact)

        (gamma, delta) match

          case (L(`0`), delta) => have(deltaF ∈ U |- 0 <= deltaF) by Weakening(lemmaForP3A of (x := deltaF))
          case (gamma, R(`1`)) => have(gammaF ∈ U |- gammaF <= 1) by Weakening(lemmaForP3B of (x := gammaF))

          // Hyp
          case (L(x1), R(y1)) if x1 == y1 => have(x1 ∈ U |- (x1 <= y1)) by Weakening(hyp of (x := x1))
          // Ax
          case _ if axioms contains (gammaF <= deltaF) => have(gammaF <= deltaF) by RewriteTrue

          // Contraction
          case (L(x1), N) if had(L(x1), L(x1)) => cutLastStep(contraction1)(x -> x1)
          // Weaken
          case (L(x1), delta) if had(L(x1), N) => cutLastStep(weaken1)(x -> x1, y -> deltaF)
          // LeftNot
          case (L(Not(x1)), delta) if had(R(x1), delta) => // no op
          // LeftAnd
          case (L(Meet(x1, y1)), delta) if had(L(x1), delta) => cutLastStep(leftAnd1)(x -> x1, y -> y1, z -> deltaF)
          case (L(Meet(x1, y1)), delta) if had(L(y1), delta) => cutLastStep(leftAnd2)(x -> x1, y -> y1, z -> deltaF)
          // LeftOr
          case (L(Join(x1, y1)), delta) if hadBoth(L(x1), delta)(L(y1), delta) =>
            cutLastStep(leftOr)(x -> x1, y -> y1, z -> deltaF)

          // Contraction
          case (N, R(x1)) if had(R(x1), R(x1)) => cutLastStep(contraction2)(x -> x1)
          // Weaken
          case (gamma, R(x1)) if had(N, R(x1)) => cutLastStep(weaken2)(x -> gammaF, y -> x1)
          // RightNot
          case (gamma, R(Not(x1))) if had(gamma, L(x1)) => // no op
          // RightOr
          case (gamma, R(Join(x1, y1))) if had(gamma, R(x1)) => cutLastStep(rightOr1)(x -> gammaF, y -> x1, z -> y1)
          case (gamma, R(Join(x1, y1))) if had(gamma, R(y1)) => cutLastStep(rightOr2)(x -> gammaF, y -> x1, z -> y1)
          // RightAnd
          case (gamma, R(Meet(x1, y1))) if hadBoth(gamma, R(x1))(gamma, R(y1)) =>
            cutLastStep(rightAnd)(x -> gammaF, y -> x1, z -> y1)

          // Commut
          case (R(x1), L(y1)) if had(L(y1), R(x1)) => cutLastStep(commutRL)(x -> y1, y -> x1)
          case (L(x1), L(y1)) if had(L(y1), L(x1)) => cutLastStep(commutLL)(x -> y1, y -> x1)
          case (R(x1), R(y1)) if had(R(y1), R(x1)) => cutLastStep(commutRR)(x -> y1, y -> x1)

          // AxCut
          case _ => axFormulas.find(x1 => hadBoth(gamma, R(x1))(L(x1), delta)) match
            case Some(cutFormula) => cutLastStep(cut)(x -> gammaF, y -> cutFormula, z -> deltaF)
            case None => return proof.InvalidProofTactic(s"No rules applied to $gamma, $delta")

      end proveNotCached

      prove(L(left), R(right)) match
        case ipt: proof.InvalidProofTactic => ipt
        case vpt: proof.ValidProofTactic =>
          val s1 = have(vpt)
          val toDischarge = s1.bot.left.collect { case in(x, `U`) if !assumedInU(x) => x }
          TacticSubproof:
            have(s1.bot) by Restate.from(s1)
            andThen(AppliedFromU.dicharge(toDischarge.toSeq *))

    end withParameters

  end RestateWithAxioms

  // ==============================================================================================
  // ======================================== TESTS ===============================================
  // ==============================================================================================

  // ================================ CAN IT PROVE THE AXIOMS ? ===================================

  val proveP1 = Theorem((O, x ∈ U) |- x <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP1

  val proveP2 = Theorem((O, x ∈ U, y ∈ U, z ∈ U, x <= y, y <= z) |- x <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP2

  val proveP3A = Theorem((O, x ∈ U) |- 0 <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP3A

  val proveP3B = Theorem((O, x ∈ U) |- x <= 1):
    have(thesis) by RestateWithAxioms.apply
  end proveP3B

  val proveP4A = Theorem((O, x ∈ U, y ∈ U) |- (x n y) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP4A

  val proveP5A = Theorem((O, x ∈ U, y ∈ U) |- (x n y) <= y):
    have(thesis) by RestateWithAxioms.apply
  end proveP5A

  val proveP4B = Theorem((O, x ∈ U, y ∈ U) |- x <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP4B

  val proveP5B = Theorem((O, x ∈ U, y ∈ U) |- y <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveP5B

  val proveP6A = Theorem((O, x ∈ U, y ∈ U, z ∈ U, x <= y, x <= z) |- x <= (y n z)):
    have(thesis) by RestateWithAxioms.apply
  end proveP6A

  val proveP6B = Theorem((O, x ∈ U, y ∈ U, z ∈ U, x <= z, y <= z) |- (x u y) <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveP6B

  val proveP7A = Theorem((O, x ∈ U) |- x <= !(!x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP7A

  val proveP7B = Theorem((O, x ∈ U) |- !(!x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end proveP7B

  val proveP8 = Theorem((O, x ∈ U, y ∈ U,  x <= y) |- !y <= !x):
    have(thesis) by RestateWithAxioms.apply
  end proveP8

  val proveP9A = Theorem((O, x ∈ U) |- (x n !x) <= 0):
    have(thesis) by RestateWithAxioms.apply
  end proveP9A

  val proveP9B = Theorem((O, x ∈ U) |- 1 <= (x u !x)):
    have(thesis) by RestateWithAxioms.apply
  end proveP9B

  // ================================== CAN IT DO REWRITES ? ======================================

  // == ALL SORT OF REWRITES OF P1

  val proveRewriteP1_1 = Theorem((O, z ∈ U) |- z <= z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_1

  val proveRewriteP1_2 = Theorem((O, z ∈ U) |- !z <= !z):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_2

  val proveRewriteP1_3 = Theorem((O, x ∈ U, y ∈ U) |- (x u y) <= (x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_3

  val proveRewriteP1_4 = Theorem((O, x ∈ U, y ∈ U) |- (x n y) <= (x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_4

  val proveRewriteP1_5 = Theorem((O, x ∈ U, y ∈ U) |- !(x u y) <= !(x u y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_5

  val proveRewriteP1_6 = Theorem((O, x ∈ U, y ∈ U) |- !(x n y) <= !(x n y)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP1_6

  // == ALL SORT OF REWRITES OF P4A

  val proveRewriteP4A_1 = Theorem((O, a ∈ U, b ∈ U) |- (a n b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_1

  val proveRewriteP4A_2 = Theorem((O, a ∈ U, b ∈ U) |- (!a n b) <= !a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_2

  val proveRewriteP4A_3 = Theorem((O, a ∈ U, b ∈ U) |- (a n !b) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_3

  val proveRewriteP4A_4 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) n c) <= (a u b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_4

  val proveRewriteP4A_5 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- (a n (b u c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_5

  val proveRewriteP4A_6 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n b)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_6

  val proveRewriteP4A_7 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= a):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP4A_7
  
  val proveRewriteP7A_1 = Theorem((O, a ∈ U) |- a <= !(!a)):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_1

  val proveRewriteP7A_2 = Theorem((O, a ∈ U) |- !a <= !(!(!a))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_2

  val proveRewriteP7A_3 = Theorem((O, a ∈ U, b ∈ U) |- (a u b) <= !(!(a u b))):
    have(thesis) by RestateWithAxioms.apply
  end proveRewriteP7A_3
  
  // =================================== NON-TRIVIAL TESTS ========================================

  val negWithLit = Theorem((O, a ∈ U) |- !a <= !0) {
    have(thesis) by RestateWithAxioms.apply
  }

  // == associativity

  val meetIsAssociative_1 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- (a n (b n c)) <= ((a n b) n c)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_1

  val meetIsAssociative_2 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- ((a n b) n c) <= (a n (b n c))):
    have(thesis) by RestateWithAxioms.apply
  end meetIsAssociative_2

  val joinIsAssociative_1 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- (a u (b u c)) <= ((a u b) u c)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_1

  val joinIsAssociative_2 = Theorem((O, a ∈ U, b ∈ U, c ∈ U) |- ((a u b) u c) <= (a u (b u c))):
    have(thesis) by RestateWithAxioms.apply
  end joinIsAssociative_2

  // == commutativity

  val meetIsCommutative = Theorem((O, a ∈ U, b ∈ U) |- (a n b) <= (b n a)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsCommutative

  val joinIsCommutative = Theorem((O, a ∈ U, b ∈ U) |- (a u b) <= (b u a)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsCommutative

  // == De Morgan's laws

  val DeMorganLaw_1 = Theorem((O, a ∈ U, b ∈ U) |- !(a u b) <= (!a n !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_1

  val DeMorganLaw_2 = Theorem((O, a ∈ U, b ∈ U) |- (!a n !b) <= !(a u b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_2

  val DeMorganLaw_3 = Theorem((O, a ∈ U, b ∈ U) |- !(a n b) <= (!a u !b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_3

  val DeMorganLaw_4 = Theorem((O, a ∈ U, b ∈ U) |- (!a u !b) <= !(a n b)):
    have(thesis) by RestateWithAxioms.apply
  end DeMorganLaw_4

  // == idempotency

  val joinIsIdempotent_1 = Theorem((O, x ∈ U) |- (x u x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_1

  val joinIsIdempotent_2 = Theorem((O, x ∈ U) |- x <= (x u x)):
    have(thesis) by RestateWithAxioms.apply
  end joinIsIdempotent_2

  val meetIsIdempotent_1 = Theorem((O, x ∈ U) |- (x n x) <= x):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_1

  val meetIsIdempotent_2 = Theorem((O, x ∈ U) |- x <= (x n x)):
    have(thesis) by RestateWithAxioms.apply
  end meetIsIdempotent_2

  // == absorption

  val absorption_1 = Theorem((O, x ∈ U, y ∈ U) |- (x u (x n y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_1

  val absorption_2 = Theorem((O, x ∈ U, y ∈ U) |- x <= (x u (x n y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_2

  val absorption_3 = Theorem((O, x ∈ U, y ∈ U) |- (x n (x u y)) <= x):
    have(thesis) by RestateWithAxioms.apply
  end absorption_3

  val absorption_4 = Theorem((O, x ∈ U, y ∈ U) |- x <= (x n (x u y))):
    have(thesis) by RestateWithAxioms.apply
  end absorption_4

  // == from paper

  val fromPaper = Theorem((O, x ∈ U, y ∈ U, 1 <= (x n (!x u y))) |- 1 <= y) :
    have(thesis) by RestateWithAxioms.apply
  end fromPaper

end OrthologicWithAxiomsST