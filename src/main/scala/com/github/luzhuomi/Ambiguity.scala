import com.github.luzhuomi.regex.Common._
import com.github.luzhuomi.regex.RE._
import com.github.luzhuomi.regex.IntPattern._


object Ambiguity 
{
	sealed trait U
	case object Nil extends U
	case object EmptyU extends U
	case class Letter(c:Char) extends U
	case class LeftU(u:U) extends U
	case class RightU(u:U) extends U
	case class Pair(u:U,v:U) extends U
	case class ListU(us:List[U]) extends U

	def nullable(r:RE)(implicit m:PosEpsilon[RE]):Boolean = m.posEpsilon(r)

	// deivative operation, the additional boolean reports whether the rule A2 arises
	def derivA2(r:RE,l:Char):(RE,Boolean) = r match 
	{
		case Phi               => (Phi,false)
		case Empty             => (Phi,false)
		case L(c) if l == c    => (Empty,false)
		case L(c)              => (Phi,false)
		case Choice(r1,r2,gf)  => 
		{
			val (r1p, b1) = derivA2(r1,l)
			val (r2p, b2) = derivA2(r2,l)
			(Choice(r1p,r2p,gf), b1 || b2)
		}
		case Seq(r1,r2) if nullable(r1) => 
		{
			val (r1p, b1) = derivA2(r1,l)
			val (r2p, b2) = derivA2(r2,l)
			(Choice(Seq(r1p,r2),r2p,Greedy), b1 || b2 || testAmbigCase1(r1)) // where A2 possibly arises	
		}
		case Seq(r1,r2) 				=> 
		{
			val (r1p, b1) = derivA2(r1,l)
			(Seq(r1p,r2), b1) 
		}
		case Star(r,gf)					=> 
		{
			val (rp,b) = derivA2(r,l)
			(Seq(rp,Star(r,gf)),b)
		}
	}

	def deriv(r:RE,l:Char):RE = derivA2(r,l)._1

	def testAmbigCase1(r:RE):Boolean = nullable(r) && (mkEmptyUs(r).length > 1)

	// For a nullable expression, compute all empty parse trees.
	def mkEmptyUs(r:RE):List[U] = r match 
	{
		case Phi   => List()
		case Empty => List(EmptyU)
		case L(_)  => List()
		case Choice(r1,r2,gf) => 
		{
			val u1s = for { u1 <- mkEmptyUs(r1); if nullable(r1) } yield LeftU(u1)
			val u2s = for { u2 <- mkEmptyUs(r2); if nullable(r2) } yield RightU(u2)
			u1s ++ u2s
		}
		case Seq(r1,r2) => for {u1 <- mkEmptyUs(r1); u2 <- mkEmptyUs(r2)} yield Pair(u1,u2)
		case Star(_,_)    => List(ListU(List()))
	}

	// Injection to obtain r's parse trees from the parse tree of the derivative.
	def injDs(r:RE, pd:RE, l:Char, u:U):List[U] = (r,pd,u) match {
		case (Star(r), Seq(rd,_), Pair(u,ListU(us))) => for 
		{
			u1 <- injDs(r,rd,l,u)
		} yield ListU(u1:us)
		case (Seq(r1,r2),Choice(Seq(rd1,_),_),LeftU(u)) => 
		{
			val Pair(up,upp) = u 
			for { us1 <- injDs(r1,rd1,l,up) } yield pair(us1,upp)
		}
		case (Seq(r1,r2),Seq(rd1,_),Pair(up,upp)) => for 
		{
			us <- injDs(r1,rd1,l,up)
		} yield Pair(us,up)

	}

}