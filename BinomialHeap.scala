import leon.lang._
import leon.collection._
import leon._
import leon.annotation._


object BinomialTree{


/* ====================   BinomialTree   ========================= */
  
  case class BinomialTree(forest: BinomialForest, value: BigInt) { 
    
    def rank: BigInt = {
      this.forest.size
    }
    
    def contents: Set[BigInt] = {
      Set(value) ++ forest.contents
    }
    
    def mergeEqual(that: BinomialTree): BinomialTree = {
      require( this.isBT && that.isBT && this.rank == that.rank && 
               equalRankLemma(this,that) )
        if (this.value > that.value) 
          BinomialTree(that.forest ++ this, that.value) 
        else 
          BinomialTree(this.forest ++ that, this.value)
    } ensuring {
      res => res.contents == this.contents ++ that.contents && res.isBT
    }
    
    def isBT: Boolean = {
      this.forest.isFull && 
      this.rank == this.forest.maxRank + 1 
    }
  }
  
  def equalRankLemma(a :BinomialTree, b: BinomialTree) = {
    require(a.isBT && b.isBT && a.rank == b.rank ) // && a.forest.isFull && b.forest.isFull)
    treeLemma(a) && treeLemma(b) && 
    (a.forest.size == b.forest.size) && 
    (a.rank == b.rank)
  }.holds
  
  def treeLemma(a :BinomialTree) = {
    require(a.isBT)
    (a.rank >= 0) && 
    (a.rank == a.forest.size) &&
    a.forest.isOrdered
  }.holds

  

/* ====================   BinomialForest   ========================= */

  abstract class BinomialForest {
    
    def minRank: BigInt = {
      require(this.isOrdered)
      this match {
        case Nil() => -1
        case Cons(h,t) => h.rank
      }
    } ensuring { res => (this.isEmpty && res == -1) || (!this.isEmpty && res >= 0) }
    
    def maxRank: BigInt = {
      require(this.isOrdered)
      this match {
        case Nil() => -1
        case Cons(h,Nil()) => h.rank
        case Cons(_,t) => t.maxRank
      }
    } ensuring { res => (!this.isEmpty && res >= 0) || (this.isEmpty && res == -1) }
    
    def size: BigInt = {
      this match {
        case Nil() => 0
        case Cons(h,t) => t.size + 1
      }
    } ensuring { _ >= 0 }
    
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
    
    // Adding a tree with a rank exactly one higher
    //@induct
    def ++(tree: BinomialTree): BinomialForest = {
      require(tree.isBT && this.isFull && ( (this.isEmpty && tree.rank == 0) || (!this.isEmpty && tree.rank == this.maxRank + 1)) )
      this match {
        case Nil() => Cons(tree,Nil())
	      case _ => this.addHelper(tree)
      }
    } ensuring {
      res => res.size == this.size + 1 && res.contents == this.contents ++ tree.contents && res.isFull
    }
    
    private def addHelper(tree: BinomialTree): BinomialForest = {
      require(tree.isBT && this.isOrdered && (this.isEmpty || tree.rank == this.maxRank + 1) )
      this match {
        case Nil() => Cons(tree,Nil())
	      case Cons(h,t) => Cons(h,t.addHelper(tree))
      }
    } ensuring {
      res => res.size == this.size + 1 && res.contents == this.contents ++ tree.contents
    }
    
    def isOrdered: Boolean = {
      this match {
        case Nil() => true
        case Cons(h,Nil()) => true
        case Cons(h,f @ Cons(h2,t) ) => if( h.rank < h2.rank ) f.isOrdered else false
      }
    } 
    
    def isCompact: Boolean = {
      this match {
        case Nil() => true
        case Cons(h,Nil()) => h.rank == this.maxRank
        case Cons(h, t @ Cons(hh,_) ) => h.rank == hh.rank + 1 && t.isCompact
      }
    }
    
    def isFull: Boolean = {
      this match {
        case Nil() => true
        case Cons(h, t ) => h.rank == 0 && isFullHelper(h.rank,t)
      }
    }
    
    def isFullHelper(rank:BigInt, tail: BinomialForest): Boolean = {
      tail match{
        case Nil() => true
        case Cons(h,t) => h.rank == rank + 1 && isFullHelper(h.rank,t)
      } 
    }
  }

  private case class Nil() extends BinomialForest
  private case class Cons(head: BinomialTree, tail: BinomialForest) extends BinomialForest

   

/* ====================   BinomialHeap   ========================= */
  
  // case class BinomialHeap(forest: BinomialForest) {
  //     def isEmpty: Boolean = {
  //       forest.isEmpty
  //     }
      
      
      
  //     def +(value: BigInt) : BinomialHeap = {
  //       this//BinomialTree(Nil(),value)
  //     }
  // }
 
  // def insertTree(tree: BinomialTree, forest: BinomialForest) : BinomialForest = {
  //   require( (tree.rank <= forest.rank) || forest.isEmpty )
  //   forest match {
  //     case Nil() => Cons(tree,Nil())
  //     case Cons(h,t) => 
  //       if( tree.rank < h.rank ) 
  //         Cons(tree,forest)
  //       else
  //         insertTree(tree.mergeEqual(h),t)
  //   }
  // }
      
  // def merge(aForest: BinomialForest, bForest: BinomialForest) : BinomialForest = {
  //   (aForest,bForest) match {
  //     case (Nil(), _) => bForest
  //     case (_, Nil()) => aForest
  //     case (a @ Cons(ah,at) , b @ Cons(bh,bt)) =>
  //       if (ah.rank > bh.rank)
  //           Cons(ah, merge(b, at))
  //       else if (ah.rank < bh.rank )
  //           Cons(bh, merge(a, bt))
  //       else
  //           insertTree( ah.mergeEqual(bh), merge(at,bt))
  //   }
  // } 
}



