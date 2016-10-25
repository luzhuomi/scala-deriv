package com.github.luzhuomi.regex.deriv.diagnosis

import com.github.luzhuomi.regex.deriv.RE._
import com.github.luzhuomi.regex.deriv.Common._

object Ambiguity 
{

	
	sealed trait U
	case object NilU extends U
	case object EmptyU extends U
	case class LetterU(c:Char) extends U
	case class AltU(i:Int,u:U) extends U
	case class PairU(u:U,v:U) extends U
	case class ListU(us:List[U]) extends U

	def nullable(r:RE)(implicit m:PosEps[RE]):Boolean = m.posEps(r)

	// deivative operation, the additional boolean reports whether the rule A2 arises
	def deriv2(r:RE,l:Char):(RE,Boolean) = r match 
	{
		case Phi               => (Phi,false)
		case Eps               => (Phi,false)
		case L(c) if l == c    => (Eps,false)
		case L(c)              => (Phi,false)
		case Any               => (Eps,false)
		case Not(cs) if !cs.contains(l) => (Eps, false)
		case Not(cs)                    => (Phi, false)
		case Choice(rs,gf)  => 
		{
			val rbs = rs map (r => deriv2(r,l))
			val (rs1, bs) = rbs.unzip
			(Choice(rs1,gf), bs.exists(b => b))
		}
		case Seq(r1,r2) if nullable(r1) => 
		{
			val (r1p, b1) = deriv2(r1,l)
			val (r2p, b2) = deriv2(r2,l)
			(Choice(List(Seq(r1p,r2),r2p),Greedy), b1 || b2 || testAmbigCase1(r1)) // where A2 possibly arises	
		}
		case Seq(r1,r2) 				=> 
		{
			val (r1p, b1) = deriv2(r1,l)
			(Seq(r1p,r2), b1) 
		}
		case Star(r,gf)					=> 
		{
			val (rp,b) = deriv2(r,l)
			(Seq(rp,Star(r,gf)),b)
		}
	}

	def deriv(r:RE,l:Char):RE = deriv2(r,l)._1

	def testAmbigCase1(r:RE):Boolean = nullable(r) && (mkEmptyUs(r).length > 1)

	// For a nullable expression, compute all empty parse trees.
	def mkEmptyUs(r:RE):List[U] = r match 
	{
		case Phi   => List()
		case Eps   => List(EmptyU)
		case Any   => List()
		case Not(_) => List()
		case L(_)  => List()
		case Choice(rs,gf) => 
		{
			val idxed_rs = (0 to rs.length).toList zip rs 
			for { (idx,r) <- idxed_rs
				; u <- mkEmptyUs(r)
				; if nullable(r) 
				} yield AltU(idx,u)
		}
		case Seq(r1,r2) => for {u1 <- mkEmptyUs(r1); u2 <- mkEmptyUs(r2)} yield PairU(u1,u2)
		case Star(_,_)  => List(ListU(List()))
	}

	// Injection to obtain r's parse trees from the parse tree of the derivative.
	// Note that the derivatives (d) can be only in shapes of (r,r), r+r, or Epsilon,
	//   hence the parse tree u can only be in shapes of Pair, LeftU, RightU or EmptyU
	def injDs(r:RE, d:RE, l:Char, u:U):List[U] = (r,d,u) match {

		case (Star(r,gf), Seq(rd,_), PairU(u,ListU(us))) => for 
		{
			u1 <- injDs(r,rd,l,u)
		} yield ListU(u1::us)
		case (Seq(r1,r2),Choice(Seq(rd1,_)::_,gf),AltU(0,u)) => 
		{ // choice must be binary b/c of deriv2
			val PairU(up,upp) = u 
			for { us1 <- injDs(r1,rd1,l,up) } yield PairU(us1,upp)
		}
		case (Seq(r1,r2),Choice(_::rd2::Nil,gf),AltU(1,u)) => for
		{ // choice must be binary b/c of deriv2
			us1 <- mkEmptyUs(r1);
			us2 <- injDs(r2,rd2,l,u)
		} yield PairU(us1,us2)
		case (Seq(r1,r2),Choice(Nil,_),_) => error ("not possible, parse tree and regex out of sync!")
		case (Seq(r1,r2),Seq(rd1,_),PairU(up,upp)) => for 
		{
			us <- injDs(r1,rd1,l,up)
		} yield PairU(us,up)
		case (Choice(r::rs,_), Choice(rd::rds,_), AltU(0,u)) => for 
		{
			us <- injDs(r,rd,l,u) 
		} yield AltU(0,us)
		case (Choice(r::rs,gf), Choice(rd::rds,gf2), AltU(n,u)) => for 
		{
			AltU(np,us) <- injDs(Choice(rs,gf),Choice(rds,gf2),l,AltU(n-1,u)) 
		} yield AltU(np+1,us)
		case (L(c), Eps, EmptyU) if (c == l) => List(LetterU(l)) 
		case (L(c), Eps, EmptyU) => error("impossible")
		case (Any, Eps, EmptyU)  => List(LetterU(l)) 
		case (Not(cs), Eps, EmptyU) if !cs.contains(l) => List(LetterU(l))
		case (Not(cs), Eps, EmptyU) => error("impossible")
	}

	// Compute alphabet of a regular expression
	def sigma(r:RE):List[Char] = r match {
		case Phi => List()
		case Eps => List()
		case L(c) => List(c)
		case Any  => List()
		case Not(cs) => List()
		case Seq(r1,r2) => (sigma(r1)++sigma(r2)).toSet.toList
		case Choice(rs,_) => rs.flatMap(sigma(_)).toSet.toList
		case Star(r,_) => sigma(r)
	}
}
