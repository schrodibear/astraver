#define false 0
#define true 1
typedef int bool;

#define pre(...) \at(__VA_ARGS__,P)
#define here(...) \at(__VA_ARGS__,H)
#define unchanged(x,y) (pre(x) == here(x) && pre(y) == here(y))
#define returns(x) assigns x; ensures \result == (x)



/********** tempomat_lever **********/

typedef enum {no_key, off, acc1, acc10, dec1, dec10, resume} tempomat_lever_t;

tempomat_lever_t tempomat_lever_port;
tempomat_lever_t tempomat_lever_previous_value = no_key;

/*@ predicate tempomat_lever_get_spec{P,H}(tempomat_lever_t result) = here(
		(pre(tempomat_lever_port != tempomat_lever_previous_value)  ==>  result == tempomat_lever_port) &&
		(pre(tempomat_lever_port == tempomat_lever_previous_value)  ==>  result == no_key));
*/
/*@	ensures tempomat_lever_get_spec{Pre,Here}(\result);
*/
tempomat_lever_t tempomat_lever_get()
{
	tempomat_lever_t result;
	tempomat_lever_t val = tempomat_lever_port;

	if(val != tempomat_lever_previous_value) {
		tempomat_lever_previous_value = val;
		return val;
	}
	else return no_key;
}



/********** sensor **********/

typedef int speed_t;
typedef int accelerator_position_t;

//@ ghost speed_t sensor_speed_result;
/*@ returns(sensor_speed_result);
	ensures 0 <= \result <= 250;
*/
speed_t sensor_speed();

//@ ghost bool sensor_brake_pedal_pressed_result;
//@ returns(sensor_brake_pedal_pressed_result);
bool sensor_brake_pedal_pressed();

//@ ghost bool sensor_engine_rpm_low_result;
//@ returns(sensor_engine_rpm_low_result);
bool sensor_engine_rpm_low();

bool sensor_driver_input_accelerate();

accelerator_position_t sensor_accelerator_position();

/********** tempomat **********/

typedef struct {
	bool active;
	bool temp_override;
	bool previously_active;
	speed_t target_speed;
	#define tempomat_min_speed 30
	#define tempomat_max_speed 250
} tempomat_t;


//@ ghost speed_t tempomat_previous_speed;
/*@ predicate tempomat_speed_range(integer speed) =
		tempomat_min_speed <= speed <= tempomat_max_speed;
	predicate tempomat_inv_speed(tempomat_t* this) =
		this->active || this->previously_active  ==>  tempomat_speed_range(this->target_speed);
	predicate tempomat_inv_prev_speed(tempomat_t* this) =
		!this->active && this->previously_active  ==>  tempomat_previous_speed == this->target_speed;
	predicate tempomat_inv0(tempomat_t* this) =
		tempomat_inv_speed(this) && tempomat_inv_prev_speed(this);
	predicate tempomat_active_no_temp_override(tempomat_t* this) =
		this->active && !this->temp_override;
*/
#define tempomat_inv_init	requires \valid(this);\
							ensures tempomat_inv0(this);
#define tempomat_inv		requires tempomat_inv0(this);\
							tempomat_inv_init


/*@	tempomat_inv_init
*/
void tempomat_init(tempomat_t* this)
{
	this->active = false;
	this->previously_active = false;
}

/*@ predicate tempomat_set_spec{P,H}(tempomat_t* this, integer speed) =
		( tempomat_speed_range(speed)  ==>  here(this->active && this->target_speed == speed)) &&
		(!tempomat_speed_range(speed)  ==>  (unchanged(this->active, this->target_speed)));
*/
/*@	tempomat_inv
	ensures tempomat_set_spec{Pre,Here}(this, speed);
*/
void tempomat_set(tempomat_t* this, speed_t speed)
{
	if(tempomat_min_speed <= speed && speed <= tempomat_max_speed) {
		this->active = true;
		this->temp_override = false;
		this->target_speed = speed;
	}
}

/*@ predicate tempomat_deactivate_spec(tempomat_t* this) =
		!this->active;
*/
/*@	requires this->active;
	tempomat_inv
	ensures tempomat_deactivate_spec(this);
*/
void tempomat_deactivate(tempomat_t* this)
{
	this->active = false;
	this->temp_override = false;
	this->previously_active = true;
	//@ ghost tempomat_previous_speed = this->target_speed;
}


//@ ghost speed_t tempomat_resume_speed;
/*@ predicate tempomat_resume_spec{P,H}(tempomat_t* this) = here(
		(pre( this->previously_active) ==> this->active && this->target_speed == tempomat_previous_speed) &&
		(pre(!this->previously_active) ==> tempomat_set_spec{P,H}(this, tempomat_resume_speed)));
*/
/*@	requires !this->active;
    tempomat_inv
	ensures tempomat_resume_spec{Pre,Here}(this);
*/
void tempomat_resume(tempomat_t* this)
{
	if(this->previously_active) this->active = true;
	else {
		tempomat_set(this, sensor_speed());
		//@ ghost tempomat_resume_speed = sensor_speed_result;
	}
}


/*@ predicate tempomat_change_speed_spec{P,H}(tempomat_t* this, integer delta) =
		tempomat_set_spec{P,H}(this, pre(this->target_speed) + delta);
*/
/*@	requires -20 <= delta <= 20;
	requires this->active;
    tempomat_inv
    ensures tempomat_change_speed_spec{Pre,Here}(this, delta);
*/
void tempomat_change_speed(tempomat_t* this, speed_t delta)
{
	tempomat_set(this, this->target_speed + delta);
}


//@ ghost tempomat_lever_t tempomat_handler_button;
//@ ghost speed_t tempomat_handler_speed;
//@ ghost bool tempomat_handler_brake_pedal_pressed;
//@ ghost bool tempomat_handler_engine_rpm_low;
//@ ghost bool tempomat_handler_driver_input_accelerate;

/*@ predicate deactivation_event =
		tempomat_handler_button == off ||
		tempomat_handler_brake_pedal_pressed ||
		tempomat_handler_engine_rpm_low ||
		(tempomat_handler_speed < tempomat_min_speed);
*/
/*@ predicate tempomat_handler_spec{P,H}(tempomat_t* this) = here(
		tempomat_lever_get_spec{P,H}(tempomat_handler_button) &&
		(deactivation_event && pre(!deactivation_event)  ==>  tempomat_deactivate_spec(this)) &&
		(pre(this->active)  ==>  (
			(!deactivation_event  ==>  (
				(tempomat_handler_button == acc1  ==>  tempomat_change_speed_spec{P,H}(this, 1))  &&
				(tempomat_handler_button == acc10  ==>  tempomat_change_speed_spec{P,H}(this, 10))  &&
				(tempomat_handler_button == dec1  ==>  tempomat_change_speed_spec{P,H}(this, -1))  &&
				(tempomat_handler_button == dec10  ==>  tempomat_change_speed_spec{P,H}(this, -10)) &&
				this->active
			)) &&
			(tempomat_handler_driver_input_accelerate  ==>  !tempomat_active_no_temp_override(this))
		)) &&
		(pre(!this->active)  ==>  (
			(tempomat_handler_button == acc1 || tempomat_handler_button == acc10 ||
				tempomat_handler_button == dec1 || tempomat_handler_button == dec10  ==>
				tempomat_set_spec{P,H}(this, tempomat_handler_speed)
			) &&
			(tempomat_handler_button == resume  ==>  tempomat_resume_spec{P,H}(this)) &&
			(tempomat_handler_button != acc1 && tempomat_handler_button != acc10 &&
				tempomat_handler_button != dec1 && tempomat_handler_button != dec10 &&
				tempomat_handler_button != resume ==>  !this->active)
		)));
*/
/*@	tempomat_inv
	ensures tempomat_handler_spec{Pre,Here}(this);
*/
void tempomat_handler(tempomat_t* this)
{
	tempomat_lever_t button = tempomat_lever_get();
	//@ ghost tempomat_handler_button = button;

	if(this->active) {
		switch(button) {
			case acc1: tempomat_change_speed(this, 1); break;
			case acc10: tempomat_change_speed(this, 10); break;
			case dec1: tempomat_change_speed(this, -1); break;
			case dec10: tempomat_change_speed(this, -10); break;
			default: /* no action*/ break;
		}
		this->temp_override = sensor_driver_input_accelerate();
		//@ ghost tempomat_handler_driver_input_accelerate = this->temp_override;
		//@ assert tempomat_handler_driver_input_accelerate  ==>  !tempomat_active_no_temp_override(this);
		if(button == off || sensor_brake_pedal_pressed() || sensor_engine_rpm_low() || sensor_speed() < tempomat_min_speed) {
			//@ ghost tempomat_handler_brake_pedal_pressed = sensor_brake_pedal_pressed_result;
			//@ ghost tempomat_handler_engine_rpm_low = sensor_engine_rpm_low_result;
			//@ ghost tempomat_handler_speed = sensor_speed_result;
			tempomat_deactivate(this);
			//@ assert !tempomat_active_no_temp_override(this);
		}
	}
	else {
		switch(button) {
			case acc1:
			case acc10:
			case dec1:
			case dec10:
				tempomat_set(this, sensor_speed());
				//@ ghost tempomat_handler_speed = sensor_speed_result;
				break;
			case resume: tempomat_resume(this); break;
			default: /* no action*/ break;
		}
	}
}



/********** electronic power control **********/

//@ ghost typedef enum {tempomat, accelerator} epc_input_mode_t;
//@ ghost epc_input_mode_t epc_input_mode;


/*@ assigns epc_input_mode;
	ensures epc_input_mode == tempomat;
*/
void epc_input_tempomat(speed_t error);


/*@ assigns epc_input_mode;
	ensures epc_input_mode == accelerator;
*/
void epc_input_manual(accelerator_position_t ap);


/********** speed_controller **********/

typedef struct {
	tempomat_t tempomat;
} speed_controller_t;


/*@ predicate speed_controller_inv0(speed_controller_t* this) =
		tempomat_inv0(&this->tempomat);
*/
#define speed_controller_inv_init	requires \valid(this) && \valid(&this->tempomat);\
									ensures speed_controller_inv0(this);
#define speed_controller_inv		requires speed_controller_inv0(this);\
									speed_controller_inv_init


/*@	speed_controller_inv_init
*/
void speed_controller_init(speed_controller_t* this)
{
	tempomat_init(&this->tempomat);
}


/*@ predicate speed_controller_run_spec{P,H}(speed_controller_t* this) = here(
		tempomat_handler_spec{P,H}(&this->tempomat) &&
		( tempomat_active_no_temp_override(&this->tempomat)  ==>  epc_input_mode == tempomat) &&
		(!tempomat_active_no_temp_override(&this->tempomat)  ==>  epc_input_mode == accelerator));
*/
/*@	speed_controller_inv
	ensures speed_controller_run_spec{Pre,Here}(this);
*/
void speed_controller_run(speed_controller_t* this)
{
	tempomat_handler(&this->tempomat);
	if((&this->tempomat)->active && !(&this->tempomat)->temp_override) {
		//@ assert tempomat_speed_range((&this->tempomat)->target_speed);
		epc_input_tempomat((&this->tempomat)->target_speed - sensor_speed());
	}
	else {
		epc_input_manual(sensor_accelerator_position());
	}
}



/********** verification **********/

/*@ speed_controller_inv
	behavior acc_dec: assumes (&this->tempomat)->active;
		ensures !deactivation_event  ==>
			(button == acc1  ==>  tempomat_change_speed_spec{Pre,Here}(&this->tempomat, 1)) &&
			(button == acc10  ==>  tempomat_change_speed_spec{Pre,Here}(&this->tempomat, 10)) &&
			(button == dec1  ==>  tempomat_change_speed_spec{Pre,Here}(&this->tempomat, -1)) &&
			(button == dec10  ==>  tempomat_change_speed_spec{Pre,Here}(&this->tempomat, -10));
	behavior set: assumes !(&this->tempomat)->active;
 		ensures button == acc1 || button == acc10 || button == dec1 || button == dec10  ==>
				tempomat_set_spec{Pre,Here}(&this->tempomat, tempomat_handler_speed);
	behavior set_resume: assumes !(&this->tempomat)->active && !(&this->tempomat)->previously_active;
 		ensures button == resume  ==>  tempomat_set_spec{Pre,Here}(&this->tempomat, tempomat_resume_speed);
	behavior resume: assumes !(&this->tempomat)->active && (&this->tempomat)->previously_active;
 		ensures button == resume  ==>  (&this->tempomat)->active && (&this->tempomat)->target_speed == tempomat_previous_speed;
 	behavior off: assumes button == off;
		ensures deactivation_event;
 	behavior remains_off: assumes !(&this->tempomat)->active;
		ensures button != acc1 && button != acc10 && button != dec1 && button != dec10 && button != resume  ==>
		!(&this->tempomat)->active;
 	behavior remains_on: assumes (&this->tempomat)->active;
		ensures !deactivation_event  ==>  (&this->tempomat)->active;
*/
void speed_controller_verify_tempomat_lever_actions(speed_controller_t* this, tempomat_lever_t button)
{
	tempomat_lever_previous_value = no_key;
	tempomat_lever_port = button;
	speed_controller_run(this);
}


/*@ speed_controller_inv
	behavior deactivate: assumes !deactivation_event;
		ensures deactivation_event  ==>  !(&this->tempomat)->active;
*/
void speed_controller_verify_deactivation(speed_controller_t* this)
{
	speed_controller_run(this);
}


/*@ speed_controller_inv
	ensures  tempomat_active_no_temp_override(&this->tempomat)  ==>  epc_input_mode == tempomat;
	ensures !tempomat_active_no_temp_override(&this->tempomat)  ==>  epc_input_mode == accelerator;
*/
void speed_controller_verify_epc_input_mode(speed_controller_t* this)
{
	speed_controller_run(this);
}


/*@ speed_controller_inv
	behavior override: assumes (&this->tempomat)->active;
		ensures tempomat_handler_driver_input_accelerate  ==>  epc_input_mode == accelerator;
*/
void speed_controller_verify_override(speed_controller_t* this)
{
	speed_controller_run(this);
}


/* 
Local Variables:
compile-command: "LC_ALL=C make bts1004.why3ml"
End:
*/
