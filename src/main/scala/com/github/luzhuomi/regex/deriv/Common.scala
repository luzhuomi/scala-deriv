package com.github.luzhuomi.regex.deriv

import scala.collection.Set

object Common
{
	sealed trait GFlag 
	case object Greedy extends GFlag
	case object NotGreedy extends GFlag

	trait PosEps[T] 
	{
		def posEps(a:T):Boolean
	}

	trait IsEps[T]
	{
		def isEps(a:T):Boolean
	}

	trait IsPhi[T]
	{
		def isPhi(a:T):Boolean
	}

	trait IsGreedy[T]
	{
		def isGreedy(t:T):Boolean
	}

	def nubBy[A,B](l:List[A], p:A=>B):List[A] = 
	{
		def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match 
		{
			case Nil => acc.reverse
			case (x::xs) if s.contains(p(x)) => go(xs,p,s,acc)
			case (x::xs)                     => go(xs,p,s+p(x),x::acc)
		}		
		go(l,p,Set.empty,Nil)
	}

	def nub[A](l:List[A]):List[A] = nubBy(l,(x:A)=>x)

}