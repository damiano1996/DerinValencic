//USERS

abstract sig User {
}

sig Username{}{
	one this.~username
}
sig Password{}{
	one this.~password
}

// CUSTOMER: people who uses the app to line up
sig Customer extends User{
	username: one Username,
	password: one Password,
        digitalticket: lone DigitalTicket,
	bookingticket: lone BookingTicket
}

fact{
	no disj a,a': Customer | a.username = a'. username
}

//PHYSICAL SPOT: The totem located in the store
sig PhysicalSpot extends User{
	physicaltickets: PhysicalSpot one -> PhysicalTicket,
	printer: one Printer
}

sig Printer{}{
	one this.~printer
}

one sig StoreManager{
	manages: one Dashboard
}

//TICKETS 

abstract sig Ticket {
	qrCode: one QRCode,
	ticketNumber: one Int, 
	state: one State,
	waitingtime: one Int
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

//RESERVATION TICKET 
sig BookingTicket{
	qrCode: lone QRCodeB
}

fact { 
	no disj t,t': BookingTicket | t.qrCode = t'.qrCode
} 


//QRCode

sig QRCode { 
	user: one User,
	time: one Int
}{
 this in ( DigitalTicket.qrCode + PhysicalTicket.qrCode)
 time > 0
}

sig QRCodeB { 
	user: one Customer,
	time: one Int
}{
 time > 0
}


// POSITION 

sig Position{
 }{
this in (DigitalTicket.gpsposition)
}

//QUEUE: List of people that are in line or rather that have a ticket

one sig Queue{ 
	contains: Int one -> Ticket,
}
//DASHBOARD: The interface that the store manager uses to control the people influx

one sig Dashboard{
        checks :one Queue,
        refers: one Store,
	controls: one Enters,
	manage: one BookingList,
	controls2:one Turnstile
}

sig QRCodeScanner {}{
	one this.~scanner
}
sig Turnstile {
	scanner: one QRCodeScanner
}{
	one this.~controls2
}


//STORE

one sig Store{
	capacity: one Int,
	peoplein: one Int,
	peopleinq: one Int,
	location: one Position,
	clock: one Int,
	departments: set Department
}{
	clock > 0
 	peoplein + peopleinq < capacity
}

// DEPARTMENT & ITEMS

sig Department{
 items: set Item
}{
	one this.~departments
}

sig Item{}{
	one this.~items
}

//STATE: Contains the states that a ticket can have 

abstract sig State{}
one sig AUTHORIZED extends State{}
one sig UNAUTHORIZED extends State{}

//ENTERS: People who are in the shop

one sig Enters{ 
	enters: Ticket set  -> lone Store,
	entersP: BookingTicket set -> lone Store
}

// BOOKING LIST : List of reservaion  
one sig BookingList{
	containsb: set BookingTicket
}{
	one this.~manage
}

//FACTS

// Associates to two attributes of store(peoplein, peopleinq)  the numbers of  istances 'enters' respectively from the Queue and from BookingList

fact NumInsideNumEnters { all s: Store | all e: Enters | s.peoplein = #e.entersP and s.peopleinq = #e.enters}

//Only people who have a ticket authorized can enter

fact Autorizedonlyifbeforeentered{ all t: Ticket | one s: Store | one a: AUTHORIZED | all e: Enters |  t -> s in e.enters implies t.state = a}

//One can enters only if he has the smallest ticket number and of the people that are not in the store and he is right on time

fact Autorizedonlyifbeforeentered2{all disj t,t': Ticket | one a: AUTHORIZED| one s: Store |   (t.ticketNumber < t'.ticketNumber and t.qrCode.time = s.clock) or ( t.ticketNumber > t'.ticketNumber  and t'.state = a and t'.qrCode.time < s.clock ) implies t.state = a } 

//If One is authorized to enter, it means that all the people with a smaller ticket number is already entered

fact OrderedEntering { all disj t,t': Ticket | one a: AUTHORIZED  |  all e: Enters | one s: Store | t.ticketNumber >  t'.ticketNumber and t.state = a  implies  t' -> s in e.enters}

// Two tickets cannot have the same qr code

fact NoSharedQR{ no disj t,t': Ticket | t.qrCode = t'.qrCode}

//Two digital tickets cannot refer to the same user

fact NoSharedUser{ no disj t,t': DigitalTicket | t.qrCode.user = t'.qrCode.user}

//Having a smaller ticket number of an another person means that the entering time is also smaller

fact TimeandNum {all disj t,t': Ticket | t.ticketNumber < t'.ticketNumber implies t.qrCode.time < t'.qrCode.time}

//Two tickets cannot have the same ticket number

fact UniqueNumberPerDay{ no disj t,t': Ticket | t.ticketNumber = t'.ticketNumber}

// The user in a digital ticket has to be a customer

fact Circle{ all d:DigitalTicket| some u:Customer |  ((u.digitalticket + d).qrCode).user = u}

// The user in a physical ticket has to be a physical spot

fact SecondCircle{ all p:PhysicalSpot | all p2:PhysicalTicket | some q: QRCode | ((p + p2).qrCode + q).user = p}

// The user in a booking ticket has to be a customer

fact ThirdCircle{ all b:BookingTicket | some u:Customer  |  ((u.bookingticket + b).qrCode).user = u}

//Il numero del ticket viene considerato dalla queue

fact RightNumbers { all q: Queue | all t: Ticket | q.contains.t = t.ticketNumber }

//If a customer is in the store it means that has the same gps location

fact InsidePosition{all e:Enters | some d: DigitalTicket | some s: Store| d -> s in e.enters implies d.gpsposition = s.location}

//Having a smaller ticket number of an another person means that the waiting time is also smaller

fact waitingTime{ all t,t': Ticket | t.ticketNumber > t'.ticketNumber implies t.waitingtime >= t'.waitingtime }

//One items can be found in only one department

fact ItemInOneDep { all d,d': Department | all i: Item | i in d.items implies i not in d'.items}

//Every person who has a booking ticket is considered inside the store if their entering time is passed

fact BTEnters {one e: Enters | some b: BookingTicket | one s: Store | b.qrCode.time < s.clock implies b -> s in e.entersP} 

//Booking tickets are always in a booking list and associated with an user

fact NoBTalone { all b: BookingTicket | some u:Customer | some bl: BookingList | b in BookingTicket implies u.bookingticket = b and b in bl.containsb}

//QRCodeB are always associated to some booking ticket

fact{  all b: BookingTicket | some q:QRCodeB | q in QRCodeB implies b.qrCode = q} 

//Assertions

//We check that if the store capacity is not reached, one person can enter, it also to show the enter predicate 

assert  EntersifNotFull { all e, e': Enters | some t,t': Ticket| one s: Store|  s.capacity > (s.peoplein + s.peopleinq) implies Entra[e, e',t,t',s]   
}

// We check that if the store capacity is reached, one person cannot enter

assert  NoEntersifFull { all e, e': Enters | some t,t': Ticket| one s: Store|  s.capacity < (s.peoplein + s.peopleinq) or s.capacity = (s.peoplein + s.peopleinq)  implies Entra[e, e',t,t',s]   
}

//We check that at most one person at a time is allowed to enter 

assert  NumPersoneAutorizzateFuori1 {one e: Enters | all t,t': Ticket | one a: AUTHORIZED | one s:Store | t.state = a and t'.state = a and t -> s not in e.enters and t' -> s not in e.enters  iff t = t' and t.state= a and t'.state = a  and t -> s not in e.enters and t' -> s not in e.enters}

//PREDS

// Eliminates one relationship 'enters' to Enters

pred Esce( e, e': Enters, t, t': Ticket, s: Store ){e'.enters = e.enters - t -> s and t'.state = UNAUTHORIZED }

// Adds one relationship 'enters' to Enters

pred Entra[e , e': Enters, t,t': Ticket, s: Store]{
	 t'-> s not in e.enters implies e'.enters = e.enters + t'-> s and t'.state = AUTHORIZED and t'.ticketNumber = t.ticketNumber
}

pred test{}

//SOME WORLDS 

//Shows clearly how the entities work with each other and that the costrains holds.
pred SmallNumber {
#DigitalTicket = 1
#Customer = 1
#QRCodeB = 1
#BookingTicket = 1
#PhysicalTicket = 0
#PhysicalSpot = 0
#Queue = 1
#Enters.enters = 0
#Enters.entersP = 0
#Department = 0
}

//Shows that the entities work with each other and that the costrains holds also for large numbers
pred BigNumbers {
#DigitalTicket = 4
#Customer = 4
#QRCodeB = 2
#BookingTicket = 2
#PhysicalTicket = 3
#PhysicalSpot = 1
#Queue = 1
#Enters.enters = 2
#Enters.entersP = 2
#Department = 2
}

//START PROGRAM


//check  EntersifNotFull

//check  NoEntersifFull

//check  NumPersoneAutorizzateFuori1

//run SmallNumber for 3

//run BigNumbers for 8
