package com.learningrx
{
   import flash.media.Sound;
   import flash.media.SoundChannel;
	import flash.media.SoundTransform;

   public class LrxSound extends Sound
	{
      private var _SoundChannel:SoundChannel;
		private var _PausePosition:int;

      public function LrxSound() 
		{
      }

      public function Play():void
		{
         _SoundChannel = this.play();
      }

      public function Stop():void
		{
         _SoundChannel.stop();
      }
		
		public function Pause():void
		{
         _PausePosition = _SoundChannel.position;
			_SoundChannel.stop();
      }

		public function Resume():void
		{
			_SoundChannel.play(_PausePosition);
      }

      public function SetPan(pPan:Number):void
		{
         var transform:SoundTransform = channel.soundTransform;
         transform.pan = pPan;
         channel.soundTransform = transform;
      }

      public function SetVolume(Volume:Number):void 
		{
         var transform:SoundTransform = _SoundChannel.soundTransform;
         transform.volume = Volume;
         _SoundChannel.soundTransform = transform;
      }
	}
}