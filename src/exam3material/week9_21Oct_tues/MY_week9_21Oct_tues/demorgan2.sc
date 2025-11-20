// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∃ x ¬P(x)   equivalent to    ¬(∀ x P(x))

@pure def demorgan2A[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      ∃((x: T) => !P(x))
    )
      |-
    (
        !(∀((x: T) => P(x)))
    )
    Proof(
      1 (  ∃((x: T) => !P(x))            ) by Premise,

      2 SubProof(
        3 Assume (∀((x: T) => P(x))),
        4 Let ((alias:T)=>SubProof(
          5 Assume (!P(alias)),
          6 (P(alias)) by AllE[T](3),
          7 (F) by NegE(6,5),
          //goal: F
        )),
        8 (F) by ExistsE[T](1,4)
        //goal: F
      ),
      9 (!(∀((x: T) => P(x)))) by NegI(2)
      //goal: !(∀((x: T) => P(x)))
    )
  )
}

@pure def demorgan2B[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      !(∀((x: T) => P(x)))
    )
      |-
    (
      ∃((x: T) => !P(x))
    )
    Proof(
      1 ( !(∀((x: T) => P(x)) )              ) by Premise,
      
      
    )
  )
}