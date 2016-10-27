package com.github.luzhuomi.regex.deriv.diagnosis

import scala.collection.Map._
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

	def isPhi(r:RE)(implicit m:IsPhi[RE]):Boolean = m.isPhi(r)

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

	def testAmigCase1(r:RE):Boolean = nullable(r) && (mkEmptyUs(r).length > 1)

	def simp(r:RE):RE = simp3(r)._1

	def simpAmbig(r:RE):Boolean = simp3(r)._3

	def simp3(r:RE):(RE,U=>List[U], Boolean) = fixs3(simpStep)(r)

	// fix point combinators working for different type signatures
	def fixs3(trans:RE => (RE, U=>List[U], Boolean)): RE => (RE, U=>List[U], Boolean) = (r:RE) =>
	{
		trans(r) match 
		{
			case (rp, f, b)	if (r == rp) => (rp,f,b)
			case (rp, f, b)              => fixs3(trans)(rp) match 
			{
				case (rpp, g, b2) => (rpp, (u:U) => 
					{
						(for { up <- g(u)
							 ; upp <- f(up)
							 } yield upp).toSet.toList
					}, 
					b || b2)
			}
		}
	}

	def fix2(trans:RE => (RE, U=>U)): RE => (RE, U => U) = (r:RE) =>
	{
		trans(r) match 
		{
			case (rp,f) if (r == rp) => (rp,f)
			case (rp,f)              => fix2(trans)(rp) match 
			{
				case (rpp,g) => (rpp, f compose g)
			}
		}
	}

	def fixs2(trans:RE => (RE, U=>List[U])): RE => (RE, U => List[U]) = (r:RE) =>
	{
		trans(r) match 
		{
			case (rp,f) if (r == rp) => (rp,f)
			case (rp,f)              => fixs2(trans)(rp) match 
			{
				case (rpp,g) => (rpp, composeT(f,g))
			}
		}
	}

	//  parse tree transformer composition
	def composeT(f:U=>List[U], g:U=>List[U]): U => List[U] = (u:U) => 
	{
		g(u).flatMap(v => f(v))
	}

	def simpStep(r:RE):(RE, U => List[U], Boolean) = r match 
	{
		case Seq(Eps, t) => simpStep(t) match 
		{
			case (rp, f, b) => (rp, (u:U) => (for { v <- f(u)} yield PairU(EmptyU,v)).toSet.toList, b)
		}
		case Seq(Phi, t) => (Phi, error("undefined"), false)
		case Choice(List(r),gf) => (r, (u:U) => List(AltU(0,u)), false)
		case Choice(rs, gf) => 
		{
			val rfbs = rs.map(simpStep)
			val (rs1,fs1,bs1) = rfbs.unzip3
			def f1(u:U):List[U] = u match 
			{
				case AltU(n,v) => for { u <- (fs1.drop(n).head)(v) } yield AltU(n,u)
				case _         => List(u) 
			}
			val b1 = bs1.exists(x=>x)
			val (r2,f2) = rmAltPhi(Choice(rs1,gf))
			val (r3,f3) = flat(r2)
			val (r4,f4,b4) =  fixs3(nubChoice)(r3)
			(r4, composeT(f1,composeT(f2,composeT(f3,f4))), b1 || b4)
		}
		case Seq(r1,r2) => 
		{
			val (r1p, f1, b1) = simpStep(r1)
			val (r2p, f2, b2) = simpStep(r2)
			def f(u:U):List[U] = u match 
			{
				case PairU(u1,u2) => for 
				{ u1p <- f1(u1)
				; u2p <- f2(u2)
				} yield PairU(u1p,u2p)
				case _            => error ("simpStep " + Seq(r1,r2).toString )
			}
			(Seq(r1p,r2p), f, b1||b2)
		}
		case _ => (r, (u:U) => List(u), false)
	}


	// remove Phi from alternatives / choice
	def rmAltPhi(r:RE):(RE, U => List[U]) = r match 
	{
		case Choice(List(rp),gf) => (r, u=>List(u))
		case Choice(rs,gf) => 
		{
			val (fs, rsp) = rmAltPhiN(0,rs).unzip
			def g(u:U):List[U] = u match 
			{
				case AltU(n,v) => List((fs.drop(n).head)(u))
			}
			(Choice(rsp,gf),g)
		}
		case _ => (r, u=>List(u))
	}
	def rmAltPhiN(n:Int,rs:List[RE]):List[(U=>U, RE)] = rs match 
	{
		case Nil => Nil
		case (r::rsp) if isPhi(r) => rmAltPhiN(n-1,rsp)
		case (r::rsp)             => (((u:U) => u match { case AltU(m,v) => AltU(n+m,v)}, r)::rmAltPhiN(n,rsp))
	}

	// flatten the nest choice at all level in the RE
	def flat(r:RE):(RE, U => List[U]) = fixs2(flatStep)(r)

	def flatStep(r:RE):(RE, U => List[U]) = r match 
	{
		case Seq(r1,r2) => 
		{
			val (r1p, f1) = flatStep(r1)
			val (r2p, f2) = flatStep(r2)
			def f(u:U):List[U] = u match 
			{
				case PairU(u1,u2) => for { u1p <- f1(u1); u2p <- f2(u2) } yield PairU(u1p,u2p)
			}
			(Seq(r1p,r2p),f)
		}
		case Choice(rs,gf) => flatChoice(r)
	}

	def flatChoice(r:RE):(RE, U => List[U]) = r match 
	{
		case Choice(List(),gf) => (r, (u:U)=>List(u))
		case Choice(r@Choice(rsI,_)::rs, gf) => 
		{
			val (Choice(rsp,_), f) = flatChoice(Choice(rs,gf))
			val l = rsI.length
			def g(u:U):List[U] = u match 
			{
				case AltU(n,v) if n < l => List(AltU(0,AltU(n,v)))
				case AltU(n,v)          => for { w <- f(rep(l,unRight,u)) } yield right(w)
			}
			(Choice(rsI++rsp,gf), g)
		}
		case Choice(r::rs,gf) => 
		{
			val (Choice(rsp,_), f) = flatChoice(Choice(rs,gf))
			def g(u:U):List[U] = u match 
			{
				case AltU(0,v) => List(AltU(0,v))
				case AltU(n,v) => for { w <- f(unRight(u))} yield right(w)
			}
			(Choice(r::rsp,gf), g)
		}
	}
	// repeatively apply op to v for i times
	def rep(i:Int,op:U=>U, v:U):U = i match 
	{
		case 0 => v
		case n => rep(n-1, op, op(v))
	}

	// add a right tag
	def right(u:U):U = u match 
	{
		case AltU(x,u) => AltU(x+1,u)
		case u         => u
	}

	// remove a right tight
	def unRight(u:U):U = u match 
	{
		case AltU(0,v) => error(" unRight is applied to a Left value.")
		case AltU(x,v) => AltU(x-1,v)
		case _         => u
	}

	// remove duplicate in a choice (apply the Idemp similarity rule)
	// Boolean denotes whether idemp rule is applied
	def nubChoice(r:RE):(RE,U=>List[U],Boolean) = r match 
	{
		case Choice(List(r1,r2), gf) if r1 == r2 => (r1, (u:U) => List(AltU(0,u),AltU(1,u)), !isPhi(r1))
		case Choice(_,_) => 
		{
			val (rp, f, m, idx, b) = nubChoiceWith(r,0, empty)
			(rp, f, b)
		}
		case _ => (r, (u:U) => List(u), false) // todo: check why this is needed
	}

	def nubChoiceWith(r:RE, idx:Int, m:Map[RE,List[Int]]):(RE, U=>List[U], Map[RE,List[Int]], Int, Boolean) = r match 
	{
		case r => (r,(u:U) => List(u), m, idx, false) // todo: check why this is needed
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