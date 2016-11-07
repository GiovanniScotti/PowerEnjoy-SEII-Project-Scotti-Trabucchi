open util/boolean

sig User {
	email: one String,
	name: one String,
	surname: one String,
	idCardNumber: one String,
	taxCode: one String,
	licenseIdNumber: one String,
	address: one String,
	phoneNumber: one Int,
	paymentMethod: one PaymentMethod,
	isAccountLocked: one Bool,
}

sig Car {
	carcode: one Int,
	status: one CarStatus,
}

sig Reservation {
	user: one User,
	reservedCar: one Car,
	reservationExpiration: one Int,
} {
	reservationExpiration >= 0 and reservationExpiration < 60
}

sig Ride {
	originLocation: one Position,
	finalLocation: lone Position,
	driver: one User,
}

sig PaymentMethod {}

sig Float {}

sig Position {
	latitude: one Float,
	longitude: one Float,
}

//The Safe Area is unique
one sig SafeArea {
	coverage: some Position,
}

abstract sig CarStatus {}
one sig AVAILABLE extends CarStatus {}
one sig OUTOFSERVICE extends CarStatus {}
one sig RESERVED extends CarStatus {}
one sig INUSE extends CarStatus {}

fact UniqueUser {
	no u1, u2: User | (u1 != u2 and
		(u1.email = u2.email or u1.idCardNumber = u2.idCardNumber or
		u1.taxCode = u2.taxCode or u1.licenseIdNumber = u2.licenseIdNumber))
}

//no users con account bloccato hanno active reservations

fact UniqueCarCode {
	no c1, c2: Car | (c1 != c2 and c1.carcode = c2.carcode)
}

assert  noCarReservedWithReservetionExpiration {
	all c: Car, res: Reservation | (c.status = RESERVED and res.reservedCar = c)
		implies (res.reservationExpiration > 0)
}

check noCarReservedWithReservetionExpiration

pred show() {
	#User >= 2
	#Ride >= 1
	#Car >= 2
}

run show for 5
