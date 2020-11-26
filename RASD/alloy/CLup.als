
// customer = real entity
// user = virtual entity

// different types of accounts
sig User {} // to represent customers

// entities to be encapsulated the the nexts
sig Printer {}
sig QRCodeScanner {}
sig Display {}
sig Turnstile {}

sig PhysicalSpot extends User {
	printer: one Printer
}
sig StoreManager extends User {
	qrCodeScanner: one QRCodeScanner,
	display: one Display,
	turnstile: one Turnstile
}

// few general entities used in the nexts
sig Date {}
sig Time {}
sig Number {}

sig QRCode { // the qr code encodes the information necessaries to identify an appointment
	user: one User,
	date: one Date,
	time: one Time
}
sig Ticket { // the ticket is the entity released to an user when it ask for a lining up,
		   // or booking a visit, operation
	qrCode: one QRCode,
	ticketNumber: one Number // used to communicate to the customers the turn
}

sig UserInLine { // to map association between user and ticket.
			  // Users that are waiting to enter in the store
	user: one User,
	ticket: one Ticket
}

abstract sig Collection {} // abstract entity to represent a general collection of entities
sig Queue extends Collection { // ordered queue of users
	users: set UserInLine
}
sig CustomersPool extends Collection { // un-ordered queue of customers inside the store
	users: set User
}

sig Store {
	// virtual entities with a real one associated:
	storeManager: one StoreManager,
	physicalSpot: one PhysicalSpot,
	// virtual representations:
	virtualQueue: one Queue, // queue of users that are waiting to enter in the store
	customersInStore: one CustomersPool // customers inside the store
}

pred show{
	#Store = 1
}

run show for 1
