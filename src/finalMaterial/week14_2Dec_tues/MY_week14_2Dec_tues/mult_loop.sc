// #Sireum #Logika


import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract? same as recursive
  Contract(
    Requires(y >= 0),
    Ensures(Res[Z] == x*y)
  )

  var total: Z = 0
  var i: Z = 0

  //what goes here?

  //automatic mode proves invariants before the loop begins

  while (i < y) {
    //what goes here?
    Invariant(
      Modifies(i, total),
      total == x*i,
      i <= y
    )
    

    //don't need to prove that the invariants are true at the end of each loop iteration

    

    //assume the invariant(s) are true here

    total = total + x

    i = i + 1

    //prove invariant(s) still true at the end of an iteration
    //want: total == x*i
    //want: i <= y

    //what should we be able to assert here?
  }

  //what do we need here?
  //don't need block to prove the post condition in auto mode

  //need: total == x*y to prove the postcondition

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

//prove precondition
//b >= 0

//don't need to prove precondition in auto mode

var ans: Z = mult(a, b)

//don't need to manually prove any asserts in auto mode

//what do we want to assert that ans is?
//need: ans == 20

assert(ans == 20)