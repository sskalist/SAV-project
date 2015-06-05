import leon.lang._
import leon.collection._
import leon._
import leon.annotation._


object BinomialTree{
  //abstract class BinomialList
  //case class Nil() extends BinomialList
  //case class Cons
  
  case class BinomialTree(forest: BinomialForest, value: BigInt) { 
    
    def rank: BigInt = {
      this.forest.rank + 1
    }
    
    def contents: Set[BigInt] = {
      Set(value) ++ forest.contents
    }
    
    //@induct
    def mergeEqual(that: BinomialTree): BinomialTree = {
      require( this.rank == that.rank && equalRank(this,that) )
        if (this.value > that.value) 
          BinomialTree(that.forest ++ this, that.value) 
        else 
          BinomialTree(this.forest ++ that, this.value)
    } ensuring {
      res => res.contents == this.contents ++ that.contents
    }
    
  }
  
  def equalRank(a :BinomialTree, b: BinomialTree) = {
    require( a.rank == b.rank)
    (a.rank >= 0) && (b.rank >= 0) && 
    (a.rank == a.forest.rank + 1) && 
    (b.rank == b.forest.rank + 1) &&
    (a.forest.rank == b.forest.rank) && 
    (a.rank == b.rank)
  }.holds
  
  abstract class BinomialForest {
    
    def rank: BigInt = {
      this match {
        case Nil() => -1
        case Cons(h,t) => t.rank + 1
      }
    } ensuring { res => (this.isEmpty && res == -1) || (!this.isEmpty && res >= 0) }
    
    def isEmpty: Boolean = {
      this match {
        case Nil() => true
        case _ => false
      }
    }
    
    def contents: Set[BigInt] = {
      this match {
        case Nil() => Set()
        case Cons(h,t) => h.contents ++ t.contents
      }
    }
    
    def ++(tree: BinomialTree): BinomialForest = {
      require(this.rank + 1 == tree.rank)
      Cons(tree,this)
    } ensuring {
      res => res.rank == tree.rank && res.contents == this.contents ++ tree.contents
    }
    
  }
  case class Nil() extends BinomialForest
  case class Cons(head: BinomialTree, tail: BinomialForest) extends BinomialForest
  
  case class BinomialHeap(forest: BinomialForest) {
      def isEmpty: Boolean = {
        forest.isEmpty
      }
      
      
      
      def +(value: BigInt) : BinomialHeap = {
        this//BinomialTree(Nil(),value)
      }
  }
 
  def insertTree(tree: BinomialTree, forest: BinomialForest) : BinomialForest = {
    require( (tree.rank <= forest.rank) || forest.isEmpty )
    forest match {
      case Nil() => Cons(tree,Nil())
      case Cons(h,t) => 
        if( tree.rank < h.rank ) 
          Cons(tree,forest)
        else
          insertTree(tree.mergeEqual(h),t)
    }
  }
      
  def merge(aForest: BinomialForest, bForest: BinomialForest) : BinomialForest = {
    (aForest,bForest) match {
      case (Nil(), _) => bForest
      case (_, Nil()) => aForest
      case (a @ Cons(ah,at) , b @ Cons(bh,bt)) =>
        if (ah.rank > bh.rank)
            Cons(ah, merge(b, at))
        else if (ah.rank < bh.rank )
            Cons(bh, merge(a, bt))
        else
            insertTree( ah.mergeEqual(bh), merge(at,bt))
    }
  } 
  
  def rankLemma(t: BinomialTree): Boolean = {
    t.forest match {
      case Nil() => t.rank == 0
      case Cons(h,Nil()) => h.rank == 1
      case Cons(h,t) => h.rank == t.rank +1
    }
  }.holds
}



