/*
* Class Definition For “KeyController”
*
*/
package com.ssink.utils.ui
{
	public class KeyController
	{
		import flash.ui.Keyboard;
		import flash.display.Stage;
		import flash.events.*;

		private const UP:Number = 0;
		private const DOWN:Number = 1;
		private const LEFT:Number = 2;
		private const RIGHT:Number = 3;
		private const JUMP:Number = 4;
		private const ATTACK:Number = 5;
		
		private var $keys:Array = undefined;
		private var $up:Number = Keyboard.UP;
		private var $down:Number = Keyboard.DOWN;
		private var $left:Number = Keyboard.LEFT;
		private var $right:Number = Keyboard.RIGHT;
		private var $jump:Number = Keyboard.SPACE;
		private var $attack:Number = Keyboard.CONTROL;
		private var $controls:Array = undefined;
		private var $ocontrols:Array = undefined;

		function KeyController()
		{
			$keys = new Array();
			$controls = new Array();
			$ocontrols = new Array();
			for (var i:Number = 0; i  <  256; ++i)
			{
				$keys[i] = false;
			}
			for (var i:Number = 0; i < 10; ++i)
			{
				$controls[i] = false;
			}
		}
		
		public static function init(stage:Stage)
		{
			stage.addEventListener(KeyboardEvent.KEY_DOWN, instance.keyDownHandler);
			stage.addEventListener(KeyboardEvent.KEY_UP, instance.keyUpHandler);
		}

		private function keyDownHandler(event:KeyboardEvent)
		{
			$keys[event.keyCode] = true;
		}

		private function keyUpHandler(event:KeyboardEvent)
		{
			$keys[event.keyCode] = false;
		}
		
		private function update()
		{
			$controls[UP] = $keys[$up];
			$controls[DOWN] = $keys[$down];
			$controls[LEFT] = $keys[$left];
			$controls[RIGHT] = $keys[$right];
			$controls[JUMP] = $keys[$jump];
			$controls[ATTACK] = $keys[$attack];
		}

		public function tick()
		{
			for(var i:Number = 0; i < $controls.length; ++i)
			{
				$ocontrols[i] = $controls[i];
			}
			update();
		}
		
		// Legacy style isDown key code check ;)
		public function isDown(n:Number)
		{
			return $keys[n];
		}
		// Digital pad keys
		public function get up():Boolean
		{
			return $controls[UP];
		}
		
		public function get down():Boolean
		{
			return $controls[DOWN];
		}
		
		public function get left():Boolean
		{
			return $controls[LEFT];
		}
		
		public function get right():Boolean
		{
			return $controls[RIGHT];
		}
		
		public function get jump():Boolean
		{
			return $controls[JUMP];
		}
		
		public function get attack():Boolean
		{
			return $controls[ATTACK];
		}
		
		// Digital pad last frame states
		public function get lup():Boolean
		{
			return $ocontrols[UP];
		}
		
		public function get ldown():Boolean
		{
			return $ocontrols[DOWN];
		}
		
		public function get lleft():Boolean
		{
			return $ocontrols[LEFT];
		}
		
		public function get lright():Boolean
		{
			return $ocontrols[RIGHT];
		}
		
		public function get ljump():Boolean
		{
			return $ocontrols[JUMP];
		}
		
		public function get lattack():Boolean
		{
			return $ocontrols[ATTACK];
		}
		
		// Setters for the keys
		public function set upKey(n:Number)
		{
			$up = n;
		}
		
		public function set downKey(n:Number)
		{
			$down = n;
		}
		
		public function set leftKey(n:Number)
		{
			$left = n;
		}
		
		public function set rightKey(n:Number)
		{
			$right = n;
		}
		
		public function set jumpKey(n:Number)
		{
			$jump = n;
		}
		
		public function set attackKey(n:Number)
		{
			$attack = n;
		}
	}
}