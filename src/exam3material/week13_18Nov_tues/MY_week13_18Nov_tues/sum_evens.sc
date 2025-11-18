// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?

  Contract(
    Requires(
      n >= 0 // doesn't make sense to add a negative number of even numbers
    )
    Ensures(
      Rez[Z] == n*(n+1)
    )
  )

  var sum: Z = 0
  var cur: Z = 0

  //need a Deduce block
  //premises: n >= 0, sum == 0, cur == 0
  //need to prove: sum == cur*(cur+1) -- invariant is true for loop begins

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur, sum),
      //at the end of each iteration how does sum relate to cur? sum == cur*(cur+1)
      //will be similar to post condition, relates to piece of post condition you have computer so far
      sum == cur*(cur+1)
    )

    cur = cur + 1

    //need a Deduce block
    //premises: cur == Old(cur) + 1
              //sum == Old(cur)*(Old(cur)+1) // invariant is true inside loop
              //Old(cur) != n
              //n >= 0
    //need: statement about the invariant without an Old
      //won't be able to prove exact invariant yet

    sum = sum + 2*cur
    //premise: sum = Old(sum) + 2*cur
             //n >= 0,
    //need: sum == cur*(cur+1)

  }

  //need: sum == n*(n+1)
  //premises: sum == cur*(cur+1), !(cur != n), n >= 0


  return sum
}

//////////// test code /////////

val num: Z = 5

//premise: num == 5
//need: num >= 0 -- whatever you are passing as parameter, if num was num-1 then num-1>=0

var sum5evens: Z = sumEvens(num)

//premise: sum5evens == num*(num+1), num == 5
//need: sum5evens == 30

//sum of first 5 evens: 30
assert(sum5evens == 30)
