// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not4(p: B, q: B, r: B): Unit = {
  Deduce(
      ( !q __>: !p )|- ( p __>: q )
      Proof(
        1 (  !q __>: !p ) by Premise,
        2 SubProof (
          3 Assume (p),
          4 SubProof(
            5 Assume (!q),
            6 (!p) by ImplyE(1, 5),
            7 (F) by NegE(3, 6)
          ),
          8 (q) by PbC(4)

          //no obvious approach, use PbC as a last resort
          //to get q

          //goal: q
        ),
        9 (p __>: q) by ImplyI(2)
        //use ImplyI
        

    )
  )
}