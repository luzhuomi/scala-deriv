package com.github.luzhuomi.regex.deriv

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
}