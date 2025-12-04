// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(
            list.size >= 1,
        ),
        //not modifying the sequence so we don't need modifies
        Ensures(
            //describe the return value
            //what we are returning is <= to all elements in the sequence
            ∀ (0 until list.size) (k => Res[Z] <= list(k)),
            
            //whatever I'm returning IS a sequence element
            ∃ (0 until list.size) (k => Res[Z] == list(k))
        ),
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),
            //bound the loop counter
            i >= 1, i <= list.size,

            //we're not changing the sequence so we don't need to say the size doesn't change

            ∀ (0 until i) (k => small <= list(k)),

            ∃ (0 until i) (k => small == list(k))
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)