package com.github.luzhuomi.regex.deriv

import com.github.luzhuomi.regex.deriv.Common._

object RE {
	sealed trait RE
	case object Phi extends RE
	case object Eps extends RE
	case class L(c:Char) extends RE
	case class Choice(rs:List[RE], gf:GFlag) extends RE
	// case class ChoiceInt(c:List[RE]) extends RE
	case class Seq(r1:RE, r2:RE) extends RE
	case class Star(r:RE, gf:GFlag) extends RE
	case object Any extends RE
	case class Not(cs:Set[Char]) extends RE


	implicit def rePosEps = new PosEps[RE] {
		def posEps(r:RE):Boolean = r match 
		{
			case Phi           => false
			case Eps           => true
			case L(_)          => false
			case Choice(rs,_)  => rs.exists(posEps)
			// case ChoiceInt(rs) => rs.exists(posEps(_))
			case Seq(r1,r2)    => posEps(r1) && posEps(r2)
			case Star(_,_)     => true
			case Any           => false
			case Not(_)        => false
		}
	}

	implicit def reIsPhi = new IsPhi[RE] {
		def isPhi(r:RE):Boolean = r match 
		{
			case Phi           => true
			case Eps           => false
			case L(_)          => false
			case Choice(rs,_)  => rs.forall(isPhi)
			case Seq(r1,r2)    => isPhi(r1) || isPhi(r2)
			case Star(_,_)     => false
			case Any           => false
			case Not(_)        => false			
		}
	}

}