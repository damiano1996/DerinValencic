//USERS
abstract sig AbsUser {
}

sig Username{}{
	one this.~username
}
sig Password{}{
	one this.~password
}

sig User extends AbsUser{ // Possiamo chiamarlo Customer?
	username: one Username,
	password: one Password,
     
	digitalticket: lone DigitalTicket, // Metterei un ticket per tutto.
	bookingticket: lone BookingTicket
}

fact{
	no disj a, a': AbsUser | a.username = a'.username
}


sig PhysicalSpot extends AbsUser{
	physicaltickets: PhysicalSpot one -> PhysicalTicket // Stesso discorso di prima: ticket unico.
	// attributi come Printer?
}

one sig StoreManager{
	manages: one Dashboard
}

//QRCode
sig QRCode { 
	user: one AbsUser,
//	date: one Date,
	time: one Int
}{
 this in ( DigitalTicket.qrCode + PhysicalTicket.qrCode + BookingTicket.qrCode)
 time > 0
}

//TICKETS 
abstract sig Ticket {
	qrCode: one QRCode,
	ticketNumber: one Int, 
	stato: one State,
	waitingtime: one Int // Secondo me non serve metterlo come attributo.
}{
     waitingtime > 0
	ticketNumber > 0
}

sig DigitalTicket extends Ticket{
	gpsposition : one Position
}{
	one this.~digitalticket
}

sig PhysicalTicket extends Ticket{}

sig BookingTicket{
	qrCode: one QRCode
}{
	one this.~bookingticket
	one this.~contieneb
}

fact { no disj t,t': BookingTicket | t.qrCode = t'.qrCode} 

// POSITION 

sig Position{
	latitude : one Int ,
	longitude : one Int
 }{
this in (DigitalTicket.gpsposition)
}

//QUEUE

one sig Queue{ 
	contiene: Int one -> Ticket,
}
//DASHBOARD

one sig Dashboard{
        gestisce :one Queue,
        riferisce: one Store,
	controls: one Enters,
	manage: one BookingList
}

//STORE

one sig Store{
	capacity: one Int ,
	peoplein: one Int,
	peopleinq: one Int,
	location: one Position,
	clock: one Int,
	departments: set Department
}{
	clock > 0
 	peoplein + peopleinq < capacity
}

// DEPARTMENT 

sig Department{
 items: set Item
}{
	one this.~departments
}

sig Item{}{
	one this.~items
}

//STATE
abstract sig State{}
one sig AUTHORIZED extends State{}
one sig UNAUTHORIZED extends State{}

//ENTERS
one sig Enters{ // da cambiare nome .-.
	entra: Ticket set  -> lone Store,
	entraP: BookingTicket set -> lone Store

// time: entra set -> one TimeofPersistence // Requirement R3
}

one sig BookingList{
	contieneb: set BookingTicket
}{
	one this.~manage
}
// TempoDentro
//sig TimeofPersistence{
// tempo: one Int
//}

//FACTS
fact NumDentroNumEntra { all s: Store | all e: Enters | s.peoplein = #e.entraP}

fact NuminQ { all s: Store | all e: Enters | s.peopleinq = #e.entra}

//fact Persona1TP1 {all e: Enters | all t: TimeofPersistence | e.entra -> t in e.time  }

fact EntranoSoloAutorizzati{ all t: Ticket | one s: Store | one a: AUTHORIZED | all e: Enters |  t -> s in e.entra implies t.stato = a}

fact AutorizzatosseQuelliPrimaEntrati{all disj t,t': Ticket | one a: AUTHORIZED| one s: Store |   (t.ticketNumber < t'.ticketNumber and t.qrCode.time = s.clock) or ( t.ticketNumber > t'.ticketNumber  and t'.stato = a and t'.qrCode.time < s.clock ) implies t.stato = a } // ~R4

fact AutorizzatosseQuelliPrimaEntrati{all disj t,t': Ticket | one a: UNAUTHORIZED| one s: Store |   !(t.ticketNumber < t'.ticketNumber and t.qrCode.time = s.clock) or !( t.ticketNumber > t'.ticketNumber  and t'.stato = a and t'.qrCode.time < s.clock) implies t.stato = a }

fact NoSharedQR{ no disj t,t': Ticket | t.qrCode = t'.qrCode}

fact TempoENum {all disj t,t': Ticket | t.ticketNumber < t'.ticketNumber implies t.qrCode.time < t'.qrCode.time}

fact UniqueNumberPerDay{ no disj t,t': Ticket | t.ticketNumber = t'.ticketNumber}

fact Circle{ all u:User | some d:DigitalTicket | some q: QRCode |  ((u.digitalticket + d).qrCode + q).user = u}

fact SecondCircle{ all p:PhysicalSpot | all p2:PhysicalTicket | some q: QRCode | ((p + p2).qrCode + q).user = p}

fact ThirdCircle{ all u:User | some b: BookingTicket | some q: QRCode |   ((u.bookingticket + b).qrCode + q).user = u}

fact NumeriGiusti { all q: Queue | all t: Ticket | q.contiene.t = t.ticketNumber }

fact posizionedentro{all e:Enters | some d: DigitalTicket | some s: Store| d -> s in e.entra implies d.gpsposition = s.location}

fact waitingTime{ all t,t': Ticket | t.ticketNumber > t'.ticketNumber implies t.waitingtime >= t'.waitingtime }

fact ItemInOneDep { all d,d': Department | all i: Item | i in d.items implies i not in d'.items}

fact BTEnters {one e: Enters | all b: BookingTicket | one s: Store | b.qrCode.time < s.clock implies b -> s in e.entraP} 
//Da mettere che le persone dentro hanno waitingtime = 0?.
// Si puo' mettere NumPeopleBefore


//PREDS
pred Esce( e, e': Enters, t, t': Ticket, s: Store ){e'.entra = e.entra - t -> s and t'.stato = UNAUTHORIZED }


pred Entra[e , e': Enters, t,t': Ticket, s: Store]{
	 t'-> s not in e.entra implies e'.entra = e.entra + t'-> s and t'.stato = AUTHORIZED and t'.ticketNumber = t.ticketNumber
}

//START PROGRAM
pred prova{}

//run Entra for 4 but exactly 3 Enters, exactly 1 Store, exactly 2 Ticket
//run Esce for 4 but exactly 3 Enters, exactly 1 Store, exactly 2 Ticket
run {prova and #DigitalTicket = 4 and #PhysicalTicket = 2 and #PhysicalSpot = 1 and #Queue = 1 and #Department = 2 and #Enters.entra = 3 and #Enters.entraP = 3} for 6 but 5 DigitalTicket, 5 PhysicalTicket
