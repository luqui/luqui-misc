package com.learningrx
{
	import flash.display.*;
	import flash.events.*;
	import flash.net.URLRequest;

	public class ImageLoader extends Sprite 
	{
		private var _Loader:Loader;
		private var _Parent:DisplayObject;
		private var _CompleteHandler:Function;
		private var _FileName:String;
		
		public function ImageLoader(pParent:DisplayObject,
									pFileName:String,
									pCompleteHandler:Function) 
		{
			//trace('ImageLoader', pParent, pFileName, pCompleteHandler);
			_Loader = new Loader();
			_Parent = pParent;
			_CompleteHandler = pCompleteHandler;
			_FileName = pFileName;
			ConfigureListeners(_Loader.contentLoaderInfo);
			_Loader.load(new URLRequest(pFileName));
			Utilities.AddChildToDisplayList(this, _Loader);
		}
		
		public function get Content():Bitmap
		{
			return _Loader.content;
		}

		public function get Parent():DisplayObject
		{
			return _Parent;
		}

		private function ConfigureListeners(pDispatcher:IEventDispatcher):void 
		{
			pDispatcher.addEventListener(Event.COMPLETE, CompleteHandler);
			pDispatcher.addEventListener(HTTPStatusEvent.HTTP_STATUS, HttpStatusHandler);
			pDispatcher.addEventListener(Event.INIT, InitHandler);
			pDispatcher.addEventListener(IOErrorEvent.IO_ERROR, IoErrorHandler);
			pDispatcher.addEventListener(Event.OPEN, OpenHandler);
			pDispatcher.addEventListener(ProgressEvent.PROGRESS, ProgressHandler);
			pDispatcher.addEventListener(Event.UNLOAD, UnLoadHandler);
		}

		private function CompleteHandler(pEvent:Event):void 
		{
			//trace('CompleteHandler', _FileName);
			_CompleteHandler();
		}

		private function HttpStatusHandler(pEvent:HTTPStatusEvent):void 
		{
			//trace("httpStatusHandler: " + pEvent);
		}

		private function InitHandler(pEvent:Event):void 
		{
			//trace("InitHandler: " + pEvent);
		}

		private function IoErrorHandler(pEvent:IOErrorEvent):void 
		{
			//trace("ioErrorHandler: " + pEvent);
		}

		private function OpenHandler(pEvent:Event):void 
		{
			//trace("openHandler: " + pEvent);
		}

		private function ProgressHandler(pEvent:ProgressEvent):void 
		{
			//trace("progressHandler: bytesLoaded=" + pEvent.bytesLoaded + " bytesTotal=" + pEvent.bytesTotal);
		}

		private function UnLoadHandler(pEvent:Event):void 
		{
			//trace("unLoadHandler: " + pEvent);
		}
	}
}