abstract sig Bool{}

one sig True extends Bool{}

one sig False extends Bool{}

sig FiscalCode{}

sig AuthorityId{}

sig Username{}

sig Password{}

sig Registration{
    username: one Username,
    password: one Password
}

abstract sig AccessRights{}

--This right allows to see the list of my reports (User right)
one sig MySignalViolations extends AccessRights{}

--This right allows to see unsafe areas (User and Authorities right)
one sig UnsafeAreaAnalysis extends AccessRights{}

--This right allows to make a report (User's right)
one sig SignalViolation extends AccessRights{}

--This right allows to see all violations (Police Officer and Municipal Director right)
one sig CheckViolations extends AccessRights{}


--This right allows to validate signalations (Police Officer right)
one sig ValidateSignalViolations extends AccessRights{}

--This right allows to see statistics (Municipal Director right)
one sig Statistics extends AccessRights{}

abstract sig Customer{
    registration: one Registration,
    accessRights: set AccessRights,
}

sig User extends Customer{
    fiscalCode: one FiscalCode,
    mySignalations: set Signalation
}

--The system automatically assigns the municipality to the third party based on its Id
abstract sig Authority extends Customer{
    id: one AuthorityId,
    municipal : one Municipality
}

sig Municipality{
    violations: set Violation
}

sig Signalation{
    violation: one Violation,
    spotter: one User,
}

sig PoliceOfficer extends Authority{
    listSignalations: set Signalation 
}

sig MunicipalEmployee extends Authority{
}

sig MunicipalDirector extends Authority{
    listViolations: set Violation
}

sig Location{
    latitude: one Int,
    longitude: one Int
}
--{latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180}
--NB: scaled valued for simplicity
{latitude >= -3 and latitude <= 3 and longitude >= -6 and longitude <= 6}

sig LicensePlate{}

sig Date {
    day: Int,
    month: Int,
    year: Int
} 
--{day > 0 and day <= 31 and month > 0 and month <= 12}
--NB: scaled valued for simplicity
{day > 0 and day <= 7 and month > 0 and month <= 3 and year > 0}


sig TimeStamp{
    date: one Date,
    hour: Int,
    minute: Int
}
--{hour >= 0 and hour < 24 and minute >= 0 and minute < 60}
--NB: scaled valued for simplicity
{hour >= 0 and hour < 2 and minute >= 0 and minute < 7}

sig Violation{
    id: one Int,
    licensePlate: one LicensePlate,
    location: one Location,
    spotter: one User,
    timestamp: one TimeStamp,
    isValid: one Bool,
    municipality: one Municipality
}
{id >= 0}
--'isValid' is put on 'True' after a check of police officer

sig Ticket{
    amount: one Int,
    violation: one Violation,
    policeOfficer: one PoliceOfficer 
}
{amount >=0}

--All Registrations have to be associated to one Customer
fact RegistrationCustomerConnection{
    all r : Registration | some c : Customer | r in c.registration
}

--The Registration has a unique Customer
fact NoSameRegistration{
    no disj c1,c2 : Customer | c1.registration = c2.registration
}

--All Usernames have to be associated to a Registration
fact UsernameRegistrationConnection{
    all u : Username | some r : Registration | u in r.username
}

--All Passwords have to be associated to a Registration
fact PasswordRegistrationConnection{
    all p : Password | some r : Registration | p in r.password
}

--Every Customer has a unique username
fact NoSameUsername{
    no disj c1,c2 : Customer | c1.registration.username = c2.registration.username
}

--All FiscalCodes must be associated to a User
fact FiscalCodeUserConnection{
    all f : FiscalCode | some u : User | f in u.fiscalCode
}

--All ThirdPartyId must be associated to an Authority
fact IdThirdPartyConnection{
    all i : AuthorityId | some t : Authority | i in t.id
}

--The Fiscal Code can be associated to only one user
fact OneUserFiscalCode{
    no disj u1,u2 : User | u1.fiscalCode = u2.fiscalCode
} 

--The id can be associated to only one authority
fact OneThirdPartyUserId{
    no disj t1, t2 : Authority | t1.id = t2.id
}

--All Date have to be associated to a TimeStamp
fact DateTimeStampConnection{
    all d : Date | some t : TimeStamp | d in t.date
}

--All LicensePlates have to be associated to a Violation
fact LicenseViolationConnection{
    all l : LicensePlate | some v : Violation | l in v.licensePlate
}

--All Timestamps have to be associated to a Violation
fact TimestampViolationConnection{
    all t : TimeStamp | some v : Violation | t in v.timestamp
}

--All Locations have to be associated to a Violation
fact LocationViolationConnection{
    all l : Location | some v : Violation | l in v.location
}

--All Violations have to be associated to a Signalation
fact ViolationSignalationConnection{
    all v : Violation | some s : Signalation | v in s.violation
}

--Only one id per violation, no replicas!
fact OneIDViolation{
    no disj v1,v2 : Violation | v1.id = v2.id
}


--It is not possible to have two different locations with the same plate and timestamp
fact SamePlateLocationAndTimestamp {
    all v1,v2 : Violation | 
    (v1.licensePlate = v2.licensePlate and v1.timestamp = v2.timestamp) implies v1.location = v2.location
}


fact PoliceOfficerRights{
    all p : PoliceOfficer | CheckViolations in p.accessRights and ValidateSignalViolations in p.accessRights and UnsafeAreaAnalysis in p.accessRights
}

fact UserRights{
    all u : User | MySignalViolations in u.accessRights and SignalViolation in u.accessRights
}

fact MunicipalEmployeeRights{
    all me : MunicipalEmployee | UnsafeAreaAnalysis in me.accessRights
}

fact MunicipalDirectorRights{
    all md : MunicipalDirector | UnsafeAreaAnalysis in md.accessRights and CheckViolations in md.accessRights and Statistics in md.accessRights
}


--Police Officer sees all the violations of his Municipality of competence
fact PoliceSeeViolations{
    all p : PoliceOfficer | all s : Signalation | p.municipal = s.violation.municipality implies s in p.listSignalations    
}

--Police Officer sees only the violations of his municipality of competence
fact PoliceDontSeeViolations{
    all p: PoliceOfficer | all s: Signalation | p.municipal != s.violation.municipality implies s not in p.listSignalations
}

--Municipal Director sees all the violations of his municipality of competence
fact MunicipalDirectorSeeViolations{
    all md : MunicipalDirector | all v : Violation | md.municipal = v.municipality implies v in md.listViolations 
}

--Municipal Director sees only the violations of his municipality of competence
fact MunicipalDirectoreDontSeeViolations{
    all md : MunicipalDirector | all v : Violation | md.municipal != v.municipality implies v not in md.listViolations
}

--All Signalations are referred to one User
fact SignalationCorrespondToOneUser{
    all s : Signalation | all u : User | (s in u.mySignalations implies s.spotter = u) and (s.spotter = u implies s in u.mySignalations) 
}

--Each Violation is referred to only one Municipality
fact ViolationOneMunicipality{
    all v : Violation | all disj m1,m2 : Municipality | v.municipality = m1 implies v not in m2.violations  
}

--All Violations are referred to Municipality
fact ViolationsOfMunicipality{
    all v : Violation | all m : Municipality | v.municipality = m implies v in m.violations   
}

--All Tickets are referred to a Signalation of the Municipality of the Police Offer who erogates the ticket
fact TicketSameMunicipalityPoliceOfficer{
    all t : Ticket | t.violation.municipality = t.policeOfficer.municipal 
}

--All Tickets are referred to a Signalation of a valid Violation
fact TicketsForValidViolation{
    all t : Ticket | t.violation.isValid = True
}

--All Municipalities are referred to a Third Party or Violation
fact MunicipalityToThirdPartyOrViolation{
    all m : Municipality | some t : Authority | m in t.municipal
}

fact SameViolationSameId{
    all v1,v2 : Violation | ((v1.licensePlate = v2.licensePlate and v1.location = v2.location and v1.timestamp.date = v2.timestamp.date) 
    implies v1.id = v2.id) and 
    (v1.id = v2.id implies (v1.licensePlate = v2.licensePlate and v1.location = v2.location))
}

--Different Police Officer of the same Municipality see the same violations
assert DifferentOfficerSameViolations{
    all disj p1, p2 : PoliceOfficer | all s1 : p1.listSignalations | all s2 : p2.listSignalations | p1.municipal = p2.municipal 
    implies (s1 in p2.listSignalations and s2 in p1.listSignalations) else (s1 not in p2.listSignalations and s2 not in p1.listSignalations)
}

check DifferentOfficerSameViolations for 10

--All the signalations are present in the list of violations of the Police Officer
assert SignalationPresentInTheList{
    all s : Signalation | all p : PoliceOfficer | s.violation.municipality = p.municipal implies s in p.listSignalations
}

check SignalationPresentInTheList for 10

--All Tickets refer to a signalation of the list signalations of the Police Officer
assert TicketFromPoliceOfficer{
    all t : Ticket | all v : Violation | some p : PoliceOfficer | v in t.violation implies v in p.listSignalations.violation 
}
check TicketFromPoliceOfficer for 10

assert TicketOnlyTrueViolation{
    no t : Ticket | t.violation.isValid = False
}
check TicketOnlyTrueViolation for 10

pred world1{
    #PoliceOfficer >= 3
    #User = 2
    (some disj p1,p2,p3 : PoliceOfficer | p1.municipal = p2.municipal and p1.municipal != p3.municipal)
}
run world1 for 10 but 0 Ticket, 0 Bool, 0 Signalation, 0 Violation, 0 AccessRights

pred world2{
    #PoliceOfficer = 2
    #Violation = 2
    #Ticket >= 1
    one v : Violation | v.isValid = False
    one v : Violation | v.isValid = True
}
run world2 for 10 but 0 AccessRights

pred world3{
    #PoliceOfficer = 2
    #User = 2
    #MunicipalDirector = 1
    #MunicipalEmployee = 2
}
run world3 for 10 but 0 Ticket, 0 Signalation, 0 Violation

pred world4{
    #PoliceOfficer = 2
    #MunicipalDirector = 1
    #User.mySignalations >=1
    all disj p1,p2 : PoliceOfficer | one d : MunicipalDirector | all s : Signalation | p1.municipal = p2.municipal and p1.municipal = d.municipal 
    and (s in p1.listSignalations implies (s in p2.listSignalations))
    and (s in p1.listSignalations implies (s.violation in d.listViolations))
    and (s in p2.listSignalations implies (s in p1.listSignalations))
    and (s.violation in d.listViolations implies (s in p1.listSignalations))
}
run world4 for 10 but 0 Ticket